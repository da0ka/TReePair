/*****************************************
	TReePair 2018.6.4
******************************************
文法圧縮の一種. 重複文脈を再帰的に圧縮していく.
記号,規則ともにCBT符号化. RePairと殆ど同じで,違いは規則の長さを符号化する事だけ.

 usage:
	TReePairing(A)
	@A	:圧縮元配列{n|0..255}
	@return	:配列{n|0..255}

	TReePaired(A)
	@A	:圧縮配列{n|0..255}
	返値	:配列{n|0..255}
******************************************/
var primes=[11,19,37,67,131,283,521,1033,2053,4099,8219,16427,32771,65581,131101,262147,524309,1048583,2097169,4194319,8388617,16777259,33554467,67108879,134217757,268435459,536870923,1073741909,0],log2=function(A,a){for(;a<255;)A[++a]=A[a>>1]+1;return A}([0],0);
function l2b(x,l){l=-1;
	if(x>255){l+=8,x>>=8;
	if(x>255){l+=8,x>>=8;
	if(x>255){l+=8,x>>=8}}}
	return l+log2[x]
}
function locatePair(Hash,left,right){
 for(var p=Hash[(1+left)*(1+right)%primes[Hash.hN]];p;p=p.link)
	if(p.left===left&&p.right===right)return p}

function buildHash(Hash,Q){
 var h,i=0,p,n=primes[++Hash.hN];Hash.length=0;
 do{
	if(++i===Q.max)i=0;
	for(p=Q[i];p;p=p.next)
	 p.link=Hash[h=(1+p.left)*(1+p.right)%n],
	 Hash[h]=p}
 while(i)}

function insertPairPQ(Q,P,n,t){
 t=Q[n<Q.max?n:n=0];Q[n]=P;P.prev=0;
 if(P.next=t)t.prev=P}

function removePairPQ(Q,P,n){
 if(P.prev){
	if(P.prev.next=P.next)P.next.prev=P.prev;return}
 if(Q[n<Q.max?n:0]=P.next)P.next.prev=0}

function destructPair(Hash,Q,P){
 var h=(1+P.left)*(1+P.right)%primes[Hash.hN],p=Hash[h],q;
 for(removePairPQ(Q,P,P.freq);p&&(p.left-P.left||p.right-P.right);p=p.link)q=p;
 q?q.link=p.link:Hash[h]=p.link;
 Q.pairs--}

function incrementPair(Q,P){
 if(P.freq>=Q.max)return++P.freq;
 removePairPQ(Q,P,P.freq);
 insertPairPQ(Q,P,++P.freq)}

function decrementPair(Hash,Q,P){
 if(P.freq>Q.max)return--P.freq;
 if(P.freq<2)return destructPair(Hash,Q,P);
 removePairPQ(Q,P,P.freq);
 insertPairPQ(Q,P,--P.freq)}

function createPair(Hash,Q,l,r,p){
 var pair={left:l,right:r,freq:1,top:p,pos:p};
 ++Q.pairs<primes[Hash.hN]||buildHash(Hash,Q);
 pair.link=Hash[p=++l*++r%primes[Hash.hN]];
 insertPairPQ(Q,Hash[p]=pair,1);
 return pair}

function resetPQ(Hash,Q,n,p){
 for(p=Q[n],Q[n]=0;p;p=n)
	n=p.next,destructPair(Hash,Q,p)}

function initRDS(Hash,Q,Code,Prev,Next){
 for(var i=0,l=Code.length-1,a,b,pair;i<l;i++)
	if(pair=locatePair(Hash,a=Code[i],b=Code[i+1]))
	 Next[Prev[i]=pair.pos]=pair.pos=i,
	 incrementPair(Q,pair);
	else createPair(Hash,Q,a,b,i);
 resetPQ(Hash,Q,1)}

function getMaxPair(Q){
 var p=Q[0],mp,m=0;
 if(p){do if(m<p.freq)m=p.freq,mp=p;while(p=p.next)}
 else{
	for(p=Q.i||Q.max-1;p>1;p--)if(mp=Q[p])break;Q.i=p}
 return mp}

function removeLinkSQ(Prev,Next,pos){
 var p=Prev[pos],n=Next[pos],u=Infinity;
 p<u&&n<u?Prev[Next[p]=n]=p:n<u?Prev[n]=u:p<u&&(Next[p]=u)}

function updateBlockSQ(Hash,Q,Code,Prev,Next,n,pos,skip){
 var l=Code.length,p=pos,lc=p,u=1/0,np=Next[p],
	lp=lc?Code[--lc]>-1?lc:Next[lc]:u,
	rp=++p<l?Code[p]>-1?p:Prev[p]:u,
	rp2=++rp<l?Code[rp]>-1?rp:Prev[rp]:u,
	r=Code[--rp];
 if(np===rp)np=Next[np];
 if(!skip&&lp<u){
	removeLinkSQ(Prev,Next,lp);
	if(p=locatePair(Hash,lc=Code[lp],Code[pos])){
	 if(p.top===lp)p.top=Next[lp];
	 decrementPair(Hash,Q,p)}
	if(p=locatePair(Hash,lc,n))
	 Next[lp]=u,
	 Next[Prev[lp]=p.pos]=p.pos=lp,
	 incrementPair(Q,p);
	else Prev[lp]=Next[lp]=u,
	 createPair(Hash,Q,lc,n,lp)}
 removeLinkSQ(Prev,Next,pos);
 removeLinkSQ(Prev,Next,rp);
 if(skip)return;
 Code[pos]=n,Code[rp]=-1;
 if(rp2<u){
	if(p=locatePair(Hash,r,r=Code[rp2])){
	 if(p.top===rp)p.top=Next[rp];
	 decrementPair(Hash,Q,p)}
	if(pos^rp2-2)
	 Prev[pos+1]=rp2,
	 Next[pos+1]=Prev[rp2-1]=u,
	 Next[rp2-1]=pos;
	else Prev[pos+1]=rp2,Next[pos+1]=pos;
	if(np>rp2)
	 if(p=locatePair(Hash,n,r))
		Next[pos]=u,
		Next[Prev[pos]=p.pos]=p.pos=pos,
		incrementPair(Q,p);
	 else Prev[pos]=Next[pos]=u,
		createPair(Hash,Q,n,r,pos);
	else Next[pos]=Prev[pos]=u}
 else if(++pos<l)
	Next[pos]=pos-1,
	Prev[pos]=Prev[rp]=Next[rp]=u}

function replace(Hash,Q,Code,Prev,Next,m,n){
 for(var i=m.top,j,l=Code.length,p,r=0,u=1/0;i<u;i=j){
	j=Next[p=i];
	if(j===(++p<l?Code[p]>-1?p:Prev[p]:u))j=Next[j];
	updateBlockSQ(Hash,Q,Code,Prev,Next,n,i,!r++&&j===u)}
 m.freq^1&&destructPair(Hash,Q,m);Q.r=r;
 resetPQ(Hash,Q,1);return r>1?r:0}

function TReePairing(A){
	function growRule(c,r,w,x){
		for(w.len+=r.len-1;w;w=w.n)
			if(w.c===c){
				for(x=w.n,w.c=r.c,w.n=r.n;w=r.n;)r=w;
				r.n=x;break
			}
		delete W[c]
	}
	function rw(c,r,s,n,u){
		if(U[u=Q[c]]>=0){
			for(e++;nc>>nl;)nl++;
			if(c>=cs)c=U[u];
			if(c<(n=(1<<nl)-nc))s=nl-1;
			else s=nl,c+=n;
			O.e(s+1,1<<s|c);d++
		}else{e--;s=W[c];
			for(n=s.len-1;rw(s.c),s=s.n;);
			if(d<3)O.e(1,0);
			else if(d<4)O.e(2,n>1);
			else{
				r=l2b(d-1),c=l2b(n),s=c+1;
				if(r=c<r)c++;
				O.e(s*2-1+r,n^!r<<c)
			}d-=n;U[u]=nc++
		}
	}
	var b=-1,c,d,e,l=0,m,n=1/0,B=0,o=A.length,cs=0,nc,nl=0,z=o,Hash=[],Code=Array(o),Prev=Array(o),Next=Array(o),W=[],O=[],Q=[],T=[],U=[];
	if(!o)return O;
	O.e=function(l,n){
		if(b>l)return B|=n<<(b-=l);
		b=32-(l-=b);
		this[o++]=(B|=n>>l)>>>24;this[o++]=B>>16&255;this[o++]=B>>8&255;this[o++]=B&255;
		if(b<32)return B=n<<b;B=0};
	for(Q.max=Math.sqrt(o)+.5|0,Q.i=Q.max-1;o;Next[o]=Prev[o]=n)U[A[--o]]=1;
	for(Hash.hN=15;++b<256;)if(U[b])U[b]=cs++;
	for(n=Q.pairs=0;n<z;)Code[n]=U[A[n++]];
	initRDS(Hash,Q,Code,Prev,Next);
	for(n=cs;m=getMaxPair(Q);m&&n++)
		b=m.left,c=m.right,
		z-=m=replace(Hash,Q,Code,Prev,Next,m,n),
		e={c:b,n:{c:c},hit:l=Q.r,len:2},
		b<cs||m&&(W[b].hit-=l-1)<2&&growRule(b,W[b],e),
		c<cs||m&&(W[c].hit-=l-1)<2&&growRule(c,W[c],e),W[n]=e;

	for(n=nc=cs;z>>++l;);
	b=32;O.e(5,l);O.e(--l,z^1<<l);

	for(c=Next=Q.length=0;c<cs;)Q[c]=c++;
	for(l=W.length;n<l;n++)W[n]&&(Q[n]=c++);
	for(O.e(1,U[l=0]>-1);n=l<256;O.e(e*2-1,n)){
		for(e=U[l]>-1;e==U[++l]>-1&&l<256;n++);
		if(n<256)for(e=0;n>>++e;);else e=5,n=0}
	for(n=U.length=cs;U[--n]=n;);
	for(;z;)if(~Code[n])d=e=0,rw(Code[n++]),O.e(1,0),z--;else n=Prev[n];
	if(b<32)for(;B;B<<=8)O[o++]=B>>>24;
	return O}

function TReePaired(A){
 A.d=function(l,n){n=B>>>32-l;
	if(l<b){if(!l)return 0;B<<=l;b-=l;return n}
	l-=b;b=32-l;
	B=this[a++]<<24|this[a++]<<16|this[a++]<<8|this[a++];
	if(l)n|=B>>>b,B<<=l;
	return n};
 for(var a=0,b=0,B,c=A.d(5)-1,d,e=0,z=A.d(c)|1<<c,l=A.d(1),m,n=0,o,r,s,O=[],R=[],S=[],T=[];e<256;l^=1){
	for(o=0;o<9&&!A.d(1);)o++;
	for(o=o<9?1<<o|A.d(o):256;o--;e++)if(l)T[n++]=e}
 if(c<0)return O;
 if(!n){for(;++o<z;)O[o]=A.d(8);return O}

 O.e=function(R,s,r){
	if(s<m)return this[++o]=T[s];
	for(r=R[s],s=r.length;s;)this.e(R,r[--s])};

 for(m=n;z--;)
	for(e=s=0;;)
	 if(A.d(1)){
		for(e++;n>>l;)l++;
		if((c=A.d(l-1))>=(d=(1<<l)-n))c+=c+A.d(1)-d;
		O.e(R,S[s++]=c)}
	 else{
		if(!--e||s<2)break;
		if(s<3)c=1;
		else if(s<4)c=1+A.d(1);
		else{
			for(c=0,d=l2b(s-1);c<d&&!A.d(1);)c++;
			c=1<<c|A.d(c)
		}r=R[n]=[];
		for(d=0;r[d++]=S[--s],c--;);S[s++]=n++}
	delete O.e;delete A.d;return O}