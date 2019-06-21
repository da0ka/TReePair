/* 
treepair --  A grammar-based compression.
(c)2018 xezz
*/
#ifdef __GNUC__

#define _FILE_OFFSET_BITS 64
#define _fseeki64 fseeko64
#define _ftelli64 ftello64

#endif // __GNUC__

#define _CRT_SECURE_CPP_OVERLOAD_STANDARD_NAMES 1
#define _CRT_SECURE_NO_WARNINGS
#define _CRT_DISABLE_PERFCRIT_LOCKS

#include<assert.h>
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include<math.h>
#include<limits.h>
#include<time.h>

#define CHAR_SIZE 256
#define NIL (CODE)-1
#define INIT_DICTIONARY_SIZE (32768)
#define DICTIONARY_SCALING_FACTOR (1.25)
#define INIT_HASH_NUM 15
#define NaN UINT_MAX

typedef unsigned int CODE;
typedef unsigned char U8;
typedef unsigned int U32;
typedef unsigned long long U64;

const char noMem[]="not enough memory";
const U32 primes[]={11,19,37,67,131,283,521,1033,2053,4099,8219,16427,32771,65581,131101,262147,524309,1048583,2097169,4194319,8388617,16777259,33554467,67108879,134217757,268435459,536870923,1073741909,0};
/////////////////////////////////////////////////////////////////////
// typedef
typedef struct Sequence{
	CODE code;
	U32 next, prev;
}SEQ;

typedef struct Pair{
	CODE left, right;
	U32 freq, f_pos, b_pos;
	struct Pair *link, *next, *prev;
}PAIR;

typedef struct Symbol{
	CODE c;
	struct Symbol *next;
}Symbol;

typedef struct Rule{
	U32 len, hit;
	Symbol *s;
}Rule;

typedef struct RePair_data_structures{
	U32 txt_len, pairs, h_num, p_max, mp;
	SEQ *seq;
	PAIR **h_first, **p_que;
}RDS;

typedef struct Dictionary{
	U32 rules, length;
	Rule *rule;
	CODE *tcode;
}DICT;
/////////////////////////////////////////////////////////////////////
// memory pool
Symbol *np=0, *nn=0;
int nodes=0;
const nLot=1024;

static inline Symbol *getNode(CODE c){
	if(!nodes)
		np=(Symbol*)malloc(sizeof(Symbol)*(nodes=nLot)),
		np->next=nn, nn=np++, --nodes;
	--nodes;
	np->c=c;np->next=0;
	return np++;
}

void freeNodes(){
	Symbol *n;
	for(nodes=0;n=nn;free(n))nn=n->next;
	np=0;
}
/////////////////////////////////////////////////////////////////////
#define toHash(P,A,B) (((A+1)*(B+1))%primes[P])

static inline PAIR *locatePair(RDS *rds, CODE left, CODE right){
	PAIR *p = rds->h_first[toHash(rds->h_num, left, right)];

	for(;p&&(p->left != left || p->right != right);p = p->link);
	return p;
}

static inline void reconstructHash(RDS *rds){
	PAIR *p, *q;
	U32 i = primes[++rds->h_num], h;
	rds->h_first = (PAIR**)realloc(rds->h_first, sizeof(PAIR*)*primes[rds->h_num]);
	for(;i;)rds->h_first[--i] = NULL;
	do{
		if(++i == rds->p_max) i = 0;
		for(p = rds->p_que[i];p;p = p->next)
			p->link = NULL,
			q = rds->h_first[h = toHash(rds->h_num, p->left, p->right)],
			rds->h_first[h] = p,
			p->link = q;
	}while(i);
}

static inline void insertPair_PQ(RDS *rds, PAIR *target, U32 p_num){
	if(p_num >= rds->p_max)p_num = 0;
	PAIR *tmp = rds->p_que[p_num];
	rds->p_que[p_num] = target;
	target->prev = NULL;
	if(target->next = tmp)tmp->prev = target;
}

static inline void removePair_PQ(RDS *rds, PAIR *target, U32 p_num){
	if(target->prev){
		if(target->prev->next = target->next)
			target->next->prev = target->prev;
		return;
	}
	if(p_num >= rds->p_max)p_num = 0;
	if(rds->p_que[p_num] = target->next)target->next->prev = NULL;
}

static inline void destructPair(RDS *rds, PAIR *o){
	U32 h = toHash(rds->h_num, o->left, o->right);
	PAIR *p = rds->h_first[h], *q = NULL;

	removePair_PQ(rds, o, o->freq);
	for(;p&&(p->left != o->left || p->right != o->right);p = p->link)q = p;

	assert(p != NULL);
	q == NULL? rds->h_first[h] = p->link: (q->link = p->link);
	free(o);
	rds->pairs--;
}

static inline void incrementPair(RDS *rds, PAIR *target){
	if(target->freq >= rds->p_max){
		++target->freq;
		return;
	}
	removePair_PQ(rds, target, target->freq);
	insertPair_PQ(rds, target, ++target->freq);
}

static inline void decrementPair(RDS *rds, PAIR *target){
	if(target->freq > rds->p_max){
		--target->freq;
		return;
	}
	if(target->freq == 1)return destructPair(rds, target);
	removePair_PQ(rds, target, target->freq);
	insertPair_PQ(rds, target, --target->freq);
}

static inline PAIR *createPair(RDS *rds, CODE left, CODE right, U32 p){
	PAIR *pair = (PAIR*)malloc(sizeof(PAIR));

	pair->left = left;
	pair->right = right;
	pair->freq = 1;
	pair->f_pos = pair->b_pos = p;
	pair->prev = pair->next = NULL;

	if(++rds->pairs >= primes[rds->h_num])reconstructHash(rds);

	pair->link = rds->h_first[p = toHash(rds->h_num, left, right)];
	insertPair_PQ(rds, rds->h_first[p] = pair, 1);
	return pair;
}

static inline void resetPQ(RDS *rds, U32 n){
	PAIR **Q = rds->p_que, *pair, *q = Q[n];
	for(Q[n] = NULL;pair = q;destructPair(rds, pair))q = q->next;
}

void initRDS(RDS *rds, int opt){
	U32 i=0, j=-1, size = rds->txt_len-1;
	SEQ *seq = rds->seq;
	CODE l, r, s=-1;
	PAIR *pair;

	for(;i<size;i++,s=l)
		if(pair = locatePair(rds, l=seq[i].code, r=seq[i+1].code)){
			if(opt==1 && l==r && l==s && i==j+1)continue;	// avoid "aaa"
			pair->b_pos = seq[seq[i].prev = pair->b_pos].next = j=i,
			incrementPair(rds, pair);
			if(opt==2)i+=l==r&&l==s;
		}else createPair(rds, l, r, j=i);
	resetPQ(rds, 1);
}

U32 createRDS(RDS *rds, SEQ *seq, FILE *ip, short *U, U32 bs, U64 *size, int opt){
	U32 c, cs=0, i=CHAR_SIZE;

	for(;i--;)U[i]=0;
	for(;++i<bs&&(c = getc(ip)) != EOF;U[seq[i].code = c]=1)seq[i].next = seq[i].prev = NaN;
	for(c=-1;++c<CHAR_SIZE;)U[c]=U[c]? cs++: -1;
	printf("input: %d, alphabet size:%d\n",i,cs);
	for(*size-=rds->txt_len=i;i--;)seq[i].code=U[seq[i].code];

	rds->pairs = rds->mp=0;
	rds->h_first = (PAIR**)calloc(sizeof(PAIR*),primes[rds->h_num=INIT_HASH_NUM]);
	rds->p_que = (PAIR**)calloc(sizeof(PAIR*),rds->p_max=1+(U32)ceil(sqrt((double)bs)));
	initRDS(rds,opt);
	return cs;
}

static inline PAIR *getMaxPair(RDS *rds){
	PAIR **p_que = rds->p_que, *p = *p_que, *best = NULL;

	if(p){
		U32 max=0;
		do if(max < p->freq)max = p->freq, best = p;while(p = p->next);
	}else{U32 i = rds->mp;
		if(!i)i = rds->p_max-1;
		for(;i>1;i--)if(best = p_que[i])break;
		rds->mp=i;
	}
	return best;
}

static inline U32 leftPos_SQ(SEQ *seq, U32 p){
	assert(p != NaN);
	if(!p)return NaN;
	if(seq[--p].code == NIL)return seq[p].next;
	return p;
}

static inline U32 rightPos_SQ(SEQ *seq, U32 p, U32 end){
	assert(p != NaN);
	if(++p == end)return NaN;
	if(seq[p].code == NIL)return seq[p].prev;
	return p;
}

static inline void removeLink_SQ(SEQ *seq, U32 target_pos){
	assert(seq[target_pos].code != NIL);
	U32 p = seq[target_pos].prev, n = seq[target_pos].next;
	p != NaN && n != NaN?(seq[seq[p].next = n].prev = p):
	n != NaN?(seq[n].prev = NaN):p != NaN&&(seq[p].next = NaN);
}

static inline void updateBlock_SQ(RDS *rds, CODE nc, U32 p, int skip){
	SEQ *seq = rds->seq;
	U32 len=rds->txt_len, lp = leftPos_SQ(seq,p), rp = rightPos_SQ(seq,p,len), rrp = rightPos_SQ(seq,rp,len), np = seq[p].next;
	CODE c = seq[p].code, rc = seq[rp].code, lc, rrc;
	PAIR *Lp, *Cp, *Rp;

	assert(c != NIL&&rc != NIL);

	if(np == rp)np = seq[np].next;
	if(!skip&&lp != NaN){
		lc = seq[lp].code;
		assert(lc != NIL);
		removeLink_SQ(seq, lp);
		if(Lp = locatePair(rds, lc, c)){
			if(Lp->f_pos == lp)Lp->f_pos = seq[lp].next;
			decrementPair(rds, Lp);
		}
		if(Lp = locatePair(rds, lc, nc))
			seq[lp].next = NaN,
			Lp->b_pos = seq[seq[lp].prev = Lp->b_pos].next = lp,
			incrementPair(rds, Lp);
		else
			seq[lp].prev = seq[lp].next = NaN,
			createPair(rds, lc, nc, lp);
	}
	removeLink_SQ(seq, p);
	removeLink_SQ(seq, rp);
	if(skip)return;
	seq[p].code = nc, seq[rp].code = NIL;
	if(rrp != NaN){
		rrc = seq[rrp].code;
		assert(rrc != NIL);
		if(Rp = locatePair(rds, rc, rrc)){
			if(Rp->f_pos == rp) Rp->f_pos = seq[rp].next;
			decrementPair(rds, Rp);
		}
		if(p == rrp-2)
			seq[p+1].prev = rrp,
			seq[p+1].next = p;
		else seq[p+1].prev = rrp,
			seq[p+1].next = seq[rrp-1].prev = NaN,
			seq[rrp-1].next = p;
		if(np > rrp){
			if(Cp = locatePair(rds, nc, rrc))
				seq[p].next = NaN,
				Cp->b_pos =seq[seq[p].prev = Cp->b_pos].next = p,
				incrementPair(rds, Cp);
			else seq[p].prev = seq[p].next = NaN,
				createPair(rds, nc, rrc, p);
		}
		else seq[p].next = seq[p].prev = NaN;
	}
	else if(++p < len){
		assert(seq[p].code == NIL);
		seq[p].next = p-1;
		seq[p].prev = seq[rp].prev = seq[rp].next = NaN;
	}
}

inline void growRule(CODE c, Rule *r, Rule *p){
	Symbol *s=p->s, *t=r->s, *x;
	for(p->len+=r->len-1;s;s=s->next)
		if(s->c==c){
			for(x=s->next,s->c=t->c,s->next=t->next;t->next;)
				t=t->next;
			t->next=x;break;
		}
	r->s=0;
}
/*
inline void growRule2(CODE c, Rule *r, Rule *p){
	Symbol *s=p->s, *t, *x;
	for(p->len+=r->len-1;s;s=s->next)
		if(s->c==c){
			for(x=s->next,t=r->s;s->c=t->c,t=t->next;)
				s=s->next=getNode(NIL);
			s->next=x;
		}
	r->s=0;
}
*/
static inline U32 replace(RDS *rds, DICT *d, PAIR *p, CODE cs, U32 *rs){
	CODE a=p->left, b=p->right, c=d->rules;
	U32 i=p->f_pos, j, len=rds->txt_len, rep = 0;
	SEQ *seq = rds->seq;

	for(;i!=NaN;i=j){
		j = seq[i].next;
		if(j == rightPos_SQ(seq,i,len))j = seq[j].next;
		updateBlock_SQ(rds,c,i,++rep<2&&j==NaN);
	}
	if(p->freq^1)destructPair(rds,p);
	resetPQ(rds,1);
	if(rep<2)return 0;
	// add rule
	Rule *R=d->rule, *r=&R[c];

	r->len = 2;r->hit = rep;
	r->s = getNode(a);r->s->next = getNode(b);

	if(a>=cs&&(R[a].hit-=rep-1)<2)growRule(a,&R[a],r), ++*rs;
	if(b>=cs&&(R[b].hit-=rep-1)<2)growRule(b,&R[b],r), ++*rs;

	if(++d->rules >= d->length){
		d->length *= DICTIONARY_SCALING_FACTOR;
		d->rule = (Rule*)realloc(R,sizeof(Rule)*d->length);
		if(d->rule == NULL)free(R), puts(noMem), exit(1);
	}
	return rep;
}

/////////////////////////////////////////////////////////////////////
inline int l2b(U32 x){
	static const U8 log2[256]={0,1,2,2,3,3,3,3,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8};
	int l=-1;
	if(x>255){l+=8;x>>=8;
	if(x>255){l+=8;x>>=8;
	if(x>255){l+=8;x>>=8;}}}
	return l+log2[x];
}

void *TReePairing(FILE *ip, FILE *op, U64 size, U32 bs, int opt){
	if(bs>size)bs=size;
	printf("	[block size:%u]\n", bs);

	PAIR *best;
	DICT *dict = (DICT*)malloc(sizeof(DICT));
	RDS *rds = (RDS*)malloc(sizeof(RDS));
	SEQ *seq = rds->seq =(SEQ*)malloc(sizeof(SEQ)*bs);
	U8 bn;
	U32 x=0, rep, ss, rs, seqlen, tlen=256, i=dict->length=INIT_DICTIONARY_SIZE;
	CODE cs, nc, *rank;
	short U[CHAR_SIZE];
	// range coder
	U8 C=0;
	U32 R=-1, N=0;
	U64 L=0;
	// models
	U8 D[128], f=128;
	U32 *E, F[12], A[31], B[31][31];	// symbol, flag, alpha, rest bits

	for(;f;)D[--f]=4096/(f+128);
	dict->rule = (Rule*)malloc(sizeof(Rule)*i);
	dict->tcode = (CODE*)malloc(sizeof(CODE)*tlen);

	inline void eb(int i, int b, U32 *P){
		U32 p=P[i]>>9, r=p>>11;
		r=(R>>12)*(r+!r);
		b?R=r:(R-=r,L+=r);r=P[i]&127;
		for(P[i]+=(((b<<23)-p)*D[r]&0xffffff80)+(r<127);R<16777216;R<<=8){
			if((L^0xff000000)>0xffffff){
				putc(C+(r=L>>32),op);
				for(r+=255;N;N--)putc(r,op);
				C=(U32)L>>24;
			}else++N;
			L=(U32)L<<8;
		}
	}

	inline void eb1(int i, int b, U32 *P){
		U32 p=P[i], r=(R>>12)*p;
		if(b)R-=r, L+=r, P[i]-=p>>4;
		else R=r, P[i]+=4096-p>>4;
		for(;R<16777216;R<<=8){
			if((L^0xff000000)>0xffffff){
				putc(C+(r=L>>32),op);
				for(r+=255;N;N--)putc(r,op);
				C=(U32)L>>24;
			}else++N;
			L=(U32)L<<8;
		}
	}

	inline void eb2(int i, int s, U32 *P){
		int b,c=1;
		for(;i;c+=c+b)eb(c,b=s>>--i&1,P);
	}

	inline void eb3(int i, int s, U32 *P){
		for(;i--;)eb(i,s>>i&1,P);
	}

	inline void eB(int i, int s){
		for(;i;){
			U32 r=R>>=1;
			if(s>>--i&1)L+=r;
			for(;R<16777216;R<<=8){
				if((L^0xff000000)>0xffffff){
					putc(C+(r=L>>32),op);
					for(r+=255;N;N--)putc(r,op);
					C=(U32)L>>24;
				}else++N;
				L=(U32)L<<8;
			}
		}
	}

	void enc(CODE c, DICT *d){	// it crashes when recursion is too many
		CODE r=rank[c];
		if(d->tcode[r] == NIL){
			Rule *R=&d->rule[c];
			Symbol *s=R->s;
			U32 n=R->len-1;

			// encode new rule
			for(ss--;enc(s->c,d),s=s->next;);
			eb(f,0,F);
			if(rs<3)f=4;	// rule stack has only 2 symbol, so no need to encode rule size
			else if(rs<4)eb(f+6,n>1,F),f=5;	// rule size is 2 or 3
			else{	// limited gamma encoding
				U32 l=n;
				for(f=c=0;l>>=1;)eb(c++,0,A);
				if(c<l2b(rs-1))eb(c,1,A);
				if(n>1)eb3(c,n,B[c-1]);
			}
			rs-=n;d->tcode[r]=nc++;
			return;
		}
		// encode symbol
		eb(f,1,F);ss++;rs++;
		for(f=1;nc>>bn;)++bn;
		if(c>=cs)c=d->tcode[r];	// non-terminal
		r=(1<<bn)-nc;
		if(c<r)eb2(bn-1,c,E);
		else c+=r, eb2(bn-1,c>>1,E), eB(1,c&1);
	}

loop:
	dict->rules = cs = createRDS(rds,seq,ip,U,bs,&size,opt);
	printf("Generating CFG(%d)... ",++x);
	for(rep=rs=0;best = getMaxPair(rds);)
		rep+=replace(rds,dict,best,cs,&rs);

	free(rds->p_que);free(rds->h_first);
	seqlen = rds->txt_len-rep;
	i=dict->rules-rs;
	if(i>=tlen)dict->tcode = (CODE*)realloc(dict->tcode, sizeof(CODE)*(tlen=i));
	printf("Done! replaced count:%u, rules:%u(-%u), seqLen:%u\nEncoding CFG...",rep,dict->rules,rs,seqlen);
	{
		U32 l=rds->txt_len, n=dict->rules, u=0;
		SEQ *seq=rds->seq;
		Rule *RL=dict->rule;
		CODE *T=dict->tcode;

		// initilize models and rank
		E=(U32*)malloc(sizeof(U32)*(n-rs)+sizeof(CODE)*n);
		rank=(CODE*)(E+n-rs);
		for(i=nc=cs;u<cs;)E[rank[u]=T[u]=u++]=1<<31;
		for(;i<n;i++)if(RL[i].s)T[u]=NIL, E[rank[i]=u++]=1<<31;
		for(f=sizeof(F)/sizeof(F[0]);f;)F[--f]=1<<31;
		for(f=sizeof(A)/sizeof(A[0]);f;A[f]=1<<31)
			for(i=f--;i;)B[f][--i]=1<<31;

		// encode size of rule & sequence
		n-=rs+cs;
		for(u=0;n>>++u;);
		eB(5,u--);eB(u,n^1<<u);
		for(u=0;seqlen>>++u;);
		eB(5,u--);eB(u,seqlen^1<<u);

		// encode char table
		for(eB(1,U[n=0]>-1);i=n<CHAR_SIZE;eB(u*2-1,i)){
			for(u=U[n]>-1;u==(U[++n]>-1)&&n<256;i++);
			if(i<256)for(u=0;i>>++u;);
			else u=5,i=0;
		}
		// encode sequence
		for(bn=0;i<l;){
			if(seq[i].code == NIL){
				i = seq[i].prev;
				continue;
			}
			ss=rs=0;	// set size of stack and rule
			enc(seq[i++].code,dict);
			eb(f,0,F);f=ss<2?2:3;
		}
		free(E);
		printf("Done! last code: %d\n", nc);
	}
	freeNodes();
	if(size)goto loop;
	// flush
	for(eB(i=5,0);i--;L=(U32)L<<8)
		if((L^0xff000000)>0xffffff){
			putc(C+(x=L>>32),op);
			for(x+=255;N;N--)putc(x,op);
			C=(U32)L>>24;
		}else++N;

	free(dict->rule);free(dict->tcode);
	free(dict);free(seq);free(rds);
}

/////////////////////////////////////////////////////////////////////

void TReePaired(FILE *ip, FILE *op, int vbs){
	U8 toChar[CHAR_SIZE];
	CODE **rule=0;
	U32 rules, seqs, cs, nc, cbits, smax=256, rmax=0;
	U32 i=128, l, n, exc, *stack=(U32*)malloc(sizeof(U32)*smax);
	// range coder
	U32 R=5, L=0;
	// models
	U8 D[128], f;
	U32 *E=0, F[12], A[31], B[31][31];	// symbol, flag, alpha, rest bits

	if(!stack)puts(noMem), exit(1);
	for(;i;)D[--i]=4096/(i+128);
	for(;R--;)L=L<<8|getc(ip);

	void dec(CODE **R, CODE c){
		if(c<cs){putc(toChar[c],op);return;}
		CODE *r=R[c-cs];
		for(c=*r;c;)dec(R,r[c--]);
	}
	inline U32 dB(int i){
		U32 b, c=0;
		for(;i--;c+=c-b){
			R>>=1;b=L-R>>31;
			for(L-=R&--b;R<16777216;R<<=8)L=L<<8|getc(ip);
		}return c;
	}
	inline U32 db(U32 *P, U32 c){
		U32 p=P[c]>>9, r=p>>11, b;
		r=(R>>12)*(r+!r), b=L<r;
		b?R=r:(R-=r,L-=r);r=P[c]&127;
		for(P[c]+=(((b<<23)-p)*D[r]&0xffffff80)+(r<127);R<16777216;R<<=8)L=L<<8|getc(ip);
		return b;
	}
	inline U32 db1(U32 *P, U32 c){
		U32 p=P[c], r=(R>>12)*p, b=L>=r;
		if(b)R-=r, L-=r, P[c]-=p>>4;
		else R=r, P[c]+=4096-p>>4;
		for(;R<16777216;R<<=8)L=L<<8|getc(ip);
		return b;
	}
	inline U32 db2(U32 *P, int i){
		U32 c=1, d=i;
		for(;i--;)c+=c+db(P,c);return c^1<<d;
	}
	inline U32 db3(U32 *P, int i){
		U32 c=0;
		for(;i--;)c|=db(P,i)<<i;return c;
	}
loop:
	n=dB(5);
	if(!n--)goto end;
	rules=1<<n|dB(n);
	n=dB(5)-1;
	seqs=1<<n|dB(n);
	n=dB(cbits=1);

	// read char table
	for(i=cs=0;i<CHAR_SIZE;n^=1){
		for(l=0;l<9&&!dB(1);++l);;
		for(l=l<9?1<<l|dB(l):256;l--;i++)if(n)toChar[cs++]=i;
	}
	if(rmax<(rules+=cs)){
		rule=(CODE**)(rule?realloc(rule,sizeof(CODE)*(rules-cs)):malloc(sizeof(CODE)*(rules-cs)));
		E=(U32*)(E?realloc(E,sizeof(U32)*rules):malloc(sizeof(U32)*rules));
		if(!rule||!E){puts(noMem);goto end;}
		for(i=rmax=rules;i;)E[--i]=1<<31;
	}else for(i=rules;i;)E[--i]=1<<31;
	vbs||printf("rules = %u, seq len = %u, alphabet = %d\n", rules, seqs, cs);

	for(f=sizeof(F)/sizeof(F[0]);f;)F[--f]=1<<31;
	for(f=sizeof(A)/sizeof(A[0]);f;A[f]=1<<31)
		for(i=f--;i;)B[f][--i]=1<<31;

	for(nc=cs;seqs--;)
		for(exc=i=0;;)
			if(db(F,f)){f=1;
				if(i>=smax){
					if((smax=i*1.25)>rmax)smax=rmax;
					stack=(U32*)realloc(stack,sizeof(U32)*smax);
					if(!stack){puts(noMem);goto end;}
				}
				for(exc++;nc>>cbits;)++cbits;
				U32 c=db2(E,cbits-1);
				if(c>=(n=(1<<cbits)-nc))c+=c+dB(1)-n;
				dec(rule,stack[i++]=c);
			}else{
				if(!--exc){f=2;break;}
				if(i<2){f=3;break;}
				if(i<3)n=1, f=4;
				else if(i<4)n=1+db(F,f+6), f=5;
				else{
					for(n=f=0,l=l2b(i-1);n<l&&!db(A,n);)n++;
					n=1<<n|db3(B[n-1],n);
				}
				CODE *r=rule[nc-cs]=(CODE*)malloc(sizeof(CODE)*-~++n);
				if(!r)puts(noMem), exit(1);
				for(*r=n;n--;)*++r=stack[--i];
				stack[i++]=nc++;
			}
	for(;nc>cs;)free(rule[--nc-cs]);
	goto loop;
end:
	if(rule)free(rule);if(stack)free(stack);if(E)free(E);
	puts("Done!");
}

/////////////////////////////////////////////////////////////////////
U32 getNum(char**c,U32 limit){U32 n=0;
 for(;*++(*c)<58&&*(*c)>47;)if(n<limit)n=n*10+(*(*c)-48);return n;}

int main(int i, char**v){
	if (i<3)usage:printf(
"TReePair compressor (c)2018 xezz\n"
"To compress: %s c[#1,#2] infile [outfile]\n"
" outfile  default name is infile.rp\n"
" #1       block size(65536 - 2147483648). default 16MB\n"
"          add 'k' means 1KB, add 'm' means 1MB\n"
" #2       optimization for first scan.\n"
"          0: nothing\n"
"          1: skip 3run length\n"
"          2: almost the same as above\n\n"
" Example:\n"
" %s c in out\n"
" %s c1m in out\n"
" %s c,1 in out\n"
" %s c1m1 in out\n\n"
"To decompress: %s d infile [outfile]\n"
" outfile  default name is infile.dp\n"
, *v,*v,*v,*v,*v,*v), exit(1);
	char *c=v[1], d=*c, *name=v[2], *name2=i<4?(char*)malloc(strlen(name)+4): v[3];
	if(!name2)puts(noMem),exit(1);

	FILE *ip, *op;
	U32 b=1<<24;
	clock_t t=clock();
	if(i<4)
		strcpy(name2, name),
		strcat(name2, d=='c'?".rp":".dp");
	if(ip = fopen(name2,"rb"))printf("Warning: overwrite [%s]\n",name2), fclose(ip);
	else printf("output = %s\n", name2);

	ip = fopen(name,"rb");
	op = fopen(name2,"wb");
	if(i<4)free(name2);
	if(!ip || !op)
		puts("File open error at the beginning."),
		exit(1);
	_fseeki64(ip,0,SEEK_END);
	U64 l = _ftelli64(ip), n;
	rewind(ip);
	if(!l)puts("0byte"), exit(1);
	if(d=='c'){
		i=0;
		if(c[1]){b=getNum(&c,1e9);
			if(*c=='k')b*=1024;
			if(*c=='m')b*=1<<20;
			if(b<1<<16)b=1<<16;
			if(b>1<<31)b=1<<31;
			if(*++c<58&&*c>47)i=*c-48;
		}TReePairing(ip,op,l,b,i);
	}else if(d=='d'||d=='D')TReePaired(ip,op,d=='d');
	else goto usage;
	n=_ftelli64(op);
	printf("size:%I64d -> %I64d (%2.2f%%, %2.2f bpb)\ntime:%2.3f s\n",l,n,100.0*n/l,8.0*n/l,(double)(clock()-t)/CLOCKS_PER_SEC);
	fclose(ip);fclose(op);
}