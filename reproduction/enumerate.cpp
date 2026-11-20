#include <algorithm>
#include <array>
#include <cstdlib>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <string>
#include <vector>
using namespace std;
constexpr int M=14;
using Bits=unsigned;
struct Counts { int q,p; };
struct Rule {int A,B,T;};
using Family=map<string,Counts>;
struct Extension {
    int n; Rule rule; Counts base;
    int s[M][M][M]={}; vector<Bits> rows[M]; Bits positive[M][M]={}, chosen[M]={};
    vector<array<int,4>> quads; Family &out;
    void put(int i,int j,int k,int bit){
        s[i][j][k]=s[j][k][i]=s[k][i][j]=bit;
        s[j][i][k]=s[i][k][j]=s[k][j][i]=1-bit;
    }
    Extension(int n, Rule r, Counts base, const string& bits, Family& out):n(n),rule(r),base(base),out(out){
        int idx=0;
        for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) for(int k=j+1;k<n;k++)put(i,j,k,bits.at(idx++)-'0');
        for(int i=0;i<n;i++)for(int j=i+1;j<n;j++)for(int k=j+1;k<n;k++)for(int l=k+1;l<n;l++)
            if(!(s[i][j][k]^s[i][j][l]^s[i][k][l]^s[j][k][l]))quads.push_back({i,j,k,l});
        if(quads.size()!=size_t(base.q))abort();
        array<Bits,M> domain={};
        for(int i=0;i<n;i++){
            set<Bits> patterns;
            for(int j=0;j<n;j++)if(i!=j){
                Bits mask=0; for(int k=0;k<n;k++)if(k!=i&&k!=j)mask|=s[i][k][j]<<k;
                Bits opposite=((1U<<n)-1)^(1U<<i)^(1U<<j);
                patterns.insert({mask,mask^(1U<<j),mask^opposite,mask^opposite^(1U<<j)});
            }
            rows[i].assign(patterns.begin(),patterns.end());
            if(rows[i].size()>=8*sizeof(Bits))abort();
            domain[i]=(1U<<rows[i].size())-1;
            for(size_t v=0;v<rows[i].size();v++)for(int j=0;j<n;j++)
                if(rows[i][v]>>j&1)positive[i][j]|=1U<<v;
        }
        visit(0,domain);
    }
    void visit(int i,array<Bits,M> domain){
        if(i==n){leaf();return;}
        for(Bits options=domain[i];options;options&=options-1){
            Bits row=rows[i][__builtin_ctz(options)]; auto next=domain; bool valid=true;
            for(int j=i+1;j<n;j++)if(!(next[j]&=(row>>j&1)?~positive[j][i]:positive[j][i])){valid=false;break;}
            if(valid){chosen[i]=row;visit(i+1,next);}
        }
    }
    string canonical(){
        string best;
        for(int i=0;i<=n;i++){
            bool hull=false;
            for(int j=0;j<=n&&!hull;j++)if(i!=j){
                int mask=0;for(int k=0;k<=n;k++)if(i!=k&&j!=k)mask|=1<<s[i][j][k];
                hull=(mask!=3);
            }
            if(!hull)continue;
            vector<int> perm={i};
            // Insertion only compares signs. Any resulting permutation gives a safe relabeling.
            for(int j=0;j<=n;j++)if(i!=j){
                auto it=perm.begin()+1;
                while(it!=perm.end()&&s[i][j][*it])it++;
                perm.insert(it,j);
            }
            for(int flip=0;flip<2;flip++){
                string bits;
                for(int a=0;a<=n;a++)for(int b=a+1;b<=n;b++)for(int c=b+1;c<=n;c++)
                    bits+=char('0'+s[perm[a]][perm[b]][perm[c]]);
                if(best.empty()||bits<best)best=bits;
                for(char &b:bits)b=(b=='0'?'1':'0');
                if(bits<best)best=bits;
                reverse(perm.begin()+1,perm.end());
            }
        }
        if(best.empty())for(int a=0;a<=n;a++)for(int b=a+1;b<=n;b++)for(int c=b+1;c<=n;c++)best+=char('0'+s[a][b][c]);
        return best;
    }
    void leaf(){
        int Q=base.q,P=base.p;
        bool convex[M][M][M]={};
        for(int a=0;a<n;a++)for(int b=a+1;b<n;b++)for(int c=b+1;c<n;c++){
            int coeff=(chosen[b]>>c&1)+(1^(chosen[a]>>c&1))+(chosen[a]>>b&1)+(1^s[a][b][c]);
            if(coeff==0||coeff==4)return;
            if(coeff==2){convex[a][b][c]=true;Q++;}
        }
        if(rule.A*Q+rule.B*P>rule.T)return;
        for(auto v:quads){auto [a,b,c,d]=v;if(convex[a][b][c]&&convex[a][b][d]&&convex[a][c][d]&&convex[b][c][d])P++;}
        if(rule.A*Q+rule.B*P>rule.T)return;
        for(int a=0;a<n;a++)for(int b=a+1;b<n;b++)put(a,b,n,chosen[a]>>b&1);
        auto result=out.emplace(canonical(),Counts{Q,P});
        if(result.first->second.q!=Q||result.first->second.p!=P)abort();
    }
};
int main(int argc,char** argv){
    if(argc!=3)return 1;
    int N=atoi(argv[1]),T=atoi(argv[2]); if(N<5||N>=M)return 1;
    Rule rules[M]={};rules[N]={1,1,T};
    for(int m=N;m>5;m--){auto [A,B,u]=rules[m];int a=A*(m-5),b=B*(m-4),g=gcd(a,b);
        rules[m-1]={a/g,b/g,u*(m-5)*(m-4)/(m*g)};}
    rules[4]={1,0,rules[5].T/(5*rules[5].A)};
    Family seeds={{"0",{0,0}}};
    for(int m=4;m<=N;m++){Family out;for(auto& seed:seeds)Extension(m-1,rules[m],seed.second,seed.first,out);
        seeds.swap(out);auto [a,b,u]=rules[m];cout<<m<<" "<<a<<" "<<b<<" "<<u<<" "<<seeds.size()<<endl;}
    if(!seeds.empty()){
        map<pair<int,int>,int> profiles;
        for(auto& seed:seeds){
            int sign[M][M][M]={},idx=0;
            for(int a=0;a<N;a++)for(int b=a+1;b<N;b++)for(int c=b+1;c<N;c++)
                sign[a][b][c]=seed.first[idx++]-'0';
            vector<bool> convex(1<<N,true);
            int Q=0,P=0,bigger=0;
            for(int set=0;set<(1<<N);set++){
                int size=__builtin_popcount(unsigned(set));if(size<4)continue;
                if(size==4){vector<int> v;for(int j=0;j<N;j++)if(set>>j&1)v.push_back(j);
                    int a=v[0],b=v[1],c=v[2],d=v[3];
                    convex[set]=!(sign[a][b][c]^sign[a][b][d]^sign[a][c][d]^sign[b][c][d]);
                }else for(int z=set;z;z&=z-1){if(!convex[set^(z&-z)]){convex[set]=false;break;}}
                if(convex[set]){if(size==4)Q++;else if(size==5)P++;else bigger++;}
            }
            if(seed.second.q!=Q||seed.second.p!=P)abort();
            profiles[{Q+P,bigger}]++;
            if(Q+P+bigger<=T)cout<<"TARGET "<<Q<<" "<<P<<" "<<bigger<<" "<<seed.first<<endl;
        }
        for(auto i:profiles)cout<<"Q+P "<<i.first.first<<" larger "<<i.first.second<<" types "<<i.second<<endl;
    }
}
