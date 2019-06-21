/*****************************************
	TReePair-rc 2018.6.9
******************************************
文法圧縮の一種. 重複文脈を再帰的に圧縮していく.
記号,規則ともにCBT符号を二値Range符号化. RePairと殆ど同じで,違いは規則の長さを符号化する事だけ.

 usage:
	TReePairing(A,lv)
	@A	:圧縮元配列{n|0..255}
	@lv	:0=fast, !0=slow but better ratio for big data
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

function TReePairing(A,lv){
	function eb(i,b,P){
		var p=(P[i]||(P[i]=0x80000000))>>>9,r=(x>>>12)*(p>>11||1);
		b?x=r:(x-=r,y+=r);
		for(P[i]+=((b<<23)-p)*Y[r=P[i]&127]&-128|r<127;x<16777216;x*=256){
			if((y^0xff000000)>>>0>0xffffff){
				O[o++]=B+(r=y/0x100000000)&255;
				for(r+=255;N;N--)O[o++]=r&255;
				B=y>>>24}
			else++N;
			y=y<<8>>>0}
	}
	function eb1(i,b,P){
		var p=(P[i]||(P[i]=2048)),r=(x>>>12)*p;
		if(b)x-=r,y+=r,P[i]-=p>>5;else x=r,P[i]+=4096-p>>5;
		for(;x<16777216;x*=256){
			if((y^0xff000000)>>>0>0xffffff){
				O[o++]=B+(r=y/0x100000000)&255;
				for(r+=255;N;N--)O[o++]=r&255;
				B=y>>>24}
			else++N;
			y=y<<8>>>0}
	}
	function eb2(i,s,P){
		for(;i;)eb(--i,s>>i&1,P)
	}
	function eb3(i,s,P){
		for(var b,c=1;i;c+=c+b)eb(c,b=s>>--i&1,P)
	}
	function eB(i,s,r){
		for(;i;){r=x>>>=1;
			if(s>>>--i&1)y+=r;
			for(;x<16777216;x*=256){
				if((y^0xff000000)>>>0>0xffffff){
					O[o++]=B+(r=y/0x100000000)&255;
					for(r+=255;N;N--)O[o++]=r&255;
					B=y>>>24}
				else++N;
				y=y<<8>>>0}
		}
	}
	function rw(c,r,s,n,t){
		if(T[t=Q[c]]>=0){d++;
			for(e++;nc>>nl;)nl++;
			if(c>=cs)c=T[t];eb(f,f=1,F);
			if(c<(n=(1<<nl)-nc))eb3(nl-1,c,E);
			else c+=n,eb3(nl-1,c>>1,E),eB(1,c&1)
		}else{e--;s=W[c];
			for(n=s.len-1;rw(s.c),s=s.n;);
			eb(f,0,F);
			if(d<3)f=4;
			else if(d<4)eb(f+6,n>1,F),f=5;
			else{f=r=0;
				for(s=n;s>>=1;)eb(r++,0,G);
				r<l2b(d-1)&&eb(r,1,G);
				n>1&&eb2(r,n,L[r])
			}d-=n;T[t]=nc++
		}
	}
	function growRule(c,r,w,x){
		for(w.len+=r.len-1;w;w=w.n)
			if(w.c===c){
				for(x=w.n,w.c=r.c,w.n=r.n;w=r.n;)r=w;
				r.n=x;break
			}
		delete W[c]
	}
	for(var b=-1,c,e,d,f=32,l=0,m,n=1/0,x=b>>>0,y=128,B=0,N=0,o=A.length,cs=0,nc,nl=o,Hash=[],Code=Array(o),Prev=Array(o),Next=Array(o),W=[],O=[],Q=[],T=[],E=[],F=[],G=[],L=[],Y=[];y;)Y[--y]=4096/(y+96)|0;
	if(!o)return O;
	for(Hash.hN=15;f;)L[--f]=[];
	if(lv)for(;o--;)E[A[o]]=1;
	else for(Q.max=Math.sqrt(o)+.5|0,Q.i=Q.max-1;o--;Next[o]=Prev[o]=n)E[A[o]]=1;
	for(;++b<256;)if(E[b])E[b]=cs++;
	for(n=Q.pairs=0;n<nl;)Code[n]=E[A[n++]];
	for(m=n=cs;T[--m]=m;);

	if(lv)m=function(C,W){	// brute force
		for(var a,c,d,w,u=cs*2;;W[u++]=d){
			for(var i=0,l=C.length-1,b=C[0],D={},best=0;i<l;b=c){
				c=C[++i];d=b*u+c;
				if(d==C[i-2]*u+b&&a==i-1)continue;
				a=D[d]=-~D[d];
				if(a>best)best=a,w=d;a=i
			}
			if(best<2)return C.length;
			d={c:c=w/u|0,n:{c:w%=u},hit:best,len:2},
			c<cs||(W[c].hit-=best-1)<2&&growRule(c,W[c],d);
			w<cs||(W[w].hit-=best-1)<2&&growRule(w,W[w],d);
			for(i=b=0;i<=l;)
				if(C[i++]^c||C[i]^w)C[b++]=C[i-1];
				else++i,C[b++]=u;C.length=b;
		}
	}(Code,W);
	else{	// faster
		for(initRDS(Hash,Q,Code,Prev,Next);m=getMaxPair(Q);)
			if(b=m.left,c=m.right,replace(Hash,Q,Code,Prev,Next,m,n))
				e={c:b,n:{c:c},hit:l=Q.r,len:2},
				b<cs||(W[b].hit-=l-1)<2&&growRule(b,W[b],e),
				c<cs||(W[c].hit-=l-1)<2&&growRule(c,W[c],e),W[n++]=e;
		for(m=n=0;n<nl;)Code[n]>-1?Code[m++]=Code[n++]:n=Prev[n];
		Code.length=m
	}
	for(c=Q.length=Prev=Next=l=0;m>>++l;);
	eB(5,l);eB(--l,m^1<<l);
	for(n=nc=cs;c<cs;)Q[c]=c++;
	for(l=W.length;n<l;n++)W[n]&&(Q[n]=c++);
	for(eB(1,E[l=0]>-1);n=l<256;eB(e*2-1,n)){
		for(e=E[l]>-1;e==E[++l]>-1&&l<256;n++);
		if(n<256)for(e=0;n>>++e;);else e=5,n=0}

	for(n=nl=E.length=0;n<m;f=e<2?2:3)d=e=0,rw(Code[n++]),eb(f,0,F);
	for(n=5;n--;y=y<<8>>>0)
		if((y^0xff000000)>>>0>0xffffff){
			O[o++]=B+(m=y/0x100000000)&255;
			for(m+=255;N;N--)O[o++]=m&255;
			B=y>>>24}
		else++N;
	return O}

function TReePaired(A){
 function dB(i,c,b){
	for(c=0;i--;c+=c-b){
		x>>>=1;b=y-x>>>31;
		for(y-=x&--b;x<16777216;x*=256)y=(y<<8|A[a++])>>>0}
	return c}

 function db(P,c){
	var p=(P[c]||(P[c]=0x80000000))>>>9,r=(x>>>12)*(p>>11||1),b=1;
	y<r?x=r:(x-=r,y-=r,b=0);
	for(P[c]+=((b<<23)-p)*Y[r=P[c]&127]&-128|r<127;x<16777216;x*=256)y=(y<<8|A[a++])>>>0;
	return b}

 function db1(P,c){
	var p=P[c]||(P[c]=2048),r=(x>>>12)*p,b=1;
	if(y<r)x=r,P[c]+=4096-p>>5,b=0;else x-=r,y-=r,P[c]-=p>>5;
	for(;x<16777216;x*=256)y=(y<<8|A[a++])>>>0;
	return b}

 function db2(P,i,c){
	for(;i--;)c|=db(P,i)<<i;return c}

 function db3(P,i,c,d){
	for(c=1,d=i;i--;)c+=c+db(P,c);return c^1<<d}

 for(var a=0,c,d,e=128,f=32,l,m,n=0,o,r,s,x=-1>>>0,y,z,O=[],E=[],F=[],G=[],L=[],R=[],S=[],T=[],Y=[];a<4;)y=(y<<8|A[a++])>>>0;
 for(c=dB(5)-1;e;)Y[--e]=4096/(e+96)|0;
 if(c<0)return O;
 for(z=dB(c)|1<<c,l=dB(1);e<256;l^=1){
	for(o=0;o<9&&!dB(1);)o++;
	for(o=o<9?1<<o|dB(o):256;o--;e++)if(l)T[n++]=e}
 if(!n){for(;++o<z;)O[o]=dB(8);return O}
 for(;f;)L[--f]=[];	// rule size model

 O.e=function(R,s,r){
	if(s<m)return this[++o]=T[s];
	for(r=R[s],s=r.length;s;)this.e(R,r[--s])};

 for(m=n;z--;)
	for(e=s=0;;)
	 if(db(F,f)){f=1;
		for(e++;n>>l;)l++;
		if((c=db3(E,l-1))>=(d=(1<<l)-n))c+=c+dB(1)-d;
		O.e(R,S[s++]=c)}
	 else{
		if(!--e){f=2;break}
		if(s<2){f=3;break}r=R[n]=[];
		if(s<3)c=1,f=4;
		else if(s<4)c=1+db(F,f+6),f=5;
		else{for(c=f=0,d=l2b(s-1);c<d&&!db(G,c);)c++;c=1<<c|db2(L[c],c)}
		for(d=0;r[d++]=S[--s],c--;);S[s++]=n++}
 delete O.e;delete A.d;return O}