class SecPoS:

    def setup(self, security_param: int = 256):
        self.p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
        self.Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
        self.Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
        self.g = (self.Gx, self.Gy)
        self.H1 = hashes.Hash(hashes.SHA256())
        self.H2 = hashes.Hash(hashes.SHA256())
        return {
            'g': self.g,
            'p': self.p,
            'H1': 'SHA256',
            'H2': 'SHA256'
        }
        
    def keygen_committee(self, num_members: int = 10):
        committee_keys = []
        for _ in range(num_members):
            pk, sk = self.pixel_plus.key_gen()
            committee_keys.append((pk, sk))
        self.committee = committee_keys
        return committee_keys
        
    def keygen_user(self):

        sk_u = secrets.randbelow(self.p)
        pk_u = self._point_multiply(self.g, sk_u)
        return (pk_u, sk_u)

    def select_roles(self, stake_holders: List[Tuple[str, int]]):
      
        sorted_holders = sorted(stake_holders, key=lambda x: x[1], reverse=True)
        miner = sorted_holders[0][0]
        leaders = [holder[0] for holder in sorted_holders[1:self.config['num_leaders']]]
        return miner, leaders
     
    def generate_block(self, prev_block):

        tx = self._generate_random_tx()
       
        if prev_block is None:
            ph = self._hash_ph([tx])
        else:
            ph = self._hash_ph([
                prev_block['tx'],
                prev_block['ph'],
                prev_block['ch'],
                prev_block['chr'],
                prev_block['cht'],
                prev_block['ts']
            ])
        ch_random = secrets.randbelow(self.p)
        ch = self._point_multiply(self.g, ch_random)
        chr_value = secrets.randbelow(self.p)
        if prev_block is None:
            cht = self.committee_public_keys
        else:
            h = self._hash_block({'tx': tx})
            h_inv = self._safe_mod_inverse(h, self.p)
            cht = self._point_subtract(prev_block['ch'], (0, chr_value))
            cht = self._point_multiply(cht, h_inv)
        block = {
            'tx': tx,
            'ph': ph,
            'ch': ch,
            'chr': chr_value,
            'cht': cht,
            'height': prev_block['height'] + 1 if prev_block else 0,
            'timestamp': int(time.time())
        }
        block_hash = self._hash_block(block)
        miner_sig = self.bls_sign(block, self.miner_key)
        leader_sigs = [self.bls_sign(block, key) for key in self.leader_keys]
        committee_sigs = [
            self.pixel_plus.sign(
                str(block).encode(),
                self.pixel_plus.current_period,
                key
            )
            for key in self.committee_keys
        ]
        block['ts'] = {
            'bls_sig': self._aggregate_bls_signatures([miner_sig] + leader_sigs),
            'pixel_sig': self.pixel_plus.aggregate_signatures(
                committee_sigs,
                self.committee_public_keys
            ),
            'apk': self.pixel_plus.aggregate_public_keys(
                self.committee_public_keys[:self.k]
            )
        }
        return block

        
    def sign_block(self, block: Dict, signer_key: rsa.RSAPrivateKey):
        block_bytes = json.dumps(block, sort_keys=True).encode()
        signature = self.pixel_plus.sign(
            block_bytes,
            self.pixel_plus.current_period,
            signer_key
        )
        return signature
        
    def verify_block(self, block):
        try:
            if block['height'] > 0:  
                expected_ph = self._hash_ph([
                    block['tx'],
                    block['ph'],
                    block['ch'],
                    block['chr'],
                    block['cht'],
                    block['ts']
                ])
                if expected_ph != block['ph']:
                    print("前序哈希验证失败")
                    return False
            if block['height'] > 0:  # 非创世区块
                tx_hash = self._hash_block({'tx': block['tx']})
                exponent = (tx_hash * block['cht'] + block['chr']) % self.p
                expected_ch = self._point_multiply(self.g, exponent)
                if expected_ch != block['ch']:
                    print("变色龙哈希验证失败")
                    return False
            h = self._hash_block(block)
            bls_sig = block['ts']['bls_sig']
            verify_point = None
            
            miner_part = self._point_multiply(self.g, (h * self.miner_key) % self.p)
            verify_point = miner_part
            for key in self.leader_keys:
                leader_part = self._point_multiply(self.g, (h * key) % self.p)
                verify_point = self._point_add(verify_point, leader_part)
            pixel_sig = block['ts']['pixel_sig']
            apk = block['ts']['apk']
            if not self._is_on_curve(pixel_sig) or not self._is_on_curve(apk):
                # print("委员会签名验证失败")
                return False
            
            return True
        
        except Exception as e:
            print(f"验证失败: {str(e)}")
            return False

    def _verify_bls_signature(self, block):
        try:
            bls_sig = block['ts']['bls_sig']
            h = self._hash_block(block)
            left = self._pairing(bls_sig, self.g)
            public_keys = []
            if block['height'] == 0:
                public_keys.append(self._point_multiply(self.g, self.miner_key))
                for key in self.leader_keys:
                    public_keys.append(self._point_multiply(self.g, key))
            else:
                public_keys = [self._point_multiply(self.g, key) for key in [self.miner_key] + self.leader_keys]
            right = None
            for pk in public_keys:
                pair = self._pairing(h, pk)
                if right is None:
                    right = pair
                else:
                    right = self._multiply_in_gt(right, pair)
            return left == right
        except Exception as e:
            print(f"BLS签名验证失败: {str(e)}")
            return False

    def _verify_pixel_signature(self, block):
        try:
            pixel_sig = block['ts']['pixel_sig']
            apk = block['ts']['apk']
            return self.pixel_plus.verify(
                str(block).encode(),
                pixel_sig,
                apk,
                self.pixel_plus.current_period
            )
        
        except Exception as e:
            print(f"Pixel+签名验证失败: {str(e)}")
            return False

    def bls_sign(self, block, private_key):
        h = self._hash_block(block)
        sig = self._point_multiply(self.g, (h * private_key) % self.p)
        return sig

    def _aggregate_bls_signatures(self, signatures):
        if not signatures:
            return None
        result = signatures[0]
        for sig in signatures[1:]:
            result = self._point_add(result, sig)
        return result
