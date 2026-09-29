#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <limits>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>

// Deterministic transport, completion, safe connector cuts, and literal Euler
// spelling. The compact input contains the accepted degree-nine parent rows
// and connector circles. No solver or factorial-sized permutation graph.
static const std::string alphabet = "0123456789ABC";
static constexpr uint32_t none = UINT32_MAX;
using Tuple = std::vector<uint8_t>;
static_assert(sizeof(size_t) >= 8, "This constructor requires a 64-bit platform.");
struct Parent { Tuple x; int deficit; };
struct Edge { uint64_t head, tail; uint32_t source, next=none; uint16_t variant; uint8_t connector; };
struct Piece { uint64_t offset,length; uint32_t root,removed; Tuple prefix,suffix; };
struct DSU {
    std::vector<uint32_t> p;
    explicit DSU(size_t n):p(n) { std::iota(p.begin(),p.end(),0); }
    uint32_t find(uint32_t x) { while(p[x]!=x){p[x]=p[p[x]];x=p[x];}return x; }
    void join(uint32_t a,uint32_t b){a=find(a);b=find(b);if(a!=b)p[b]=a;}
};
static void require(bool ok,const char* text){if(!ok)throw std::runtime_error(text);}
static uint64_t factorial(int n){uint64_t v=1;for(int j=2;j<=n;++j)v*=j;return v;}
static Tuple rotate(const Tuple& x,int k){Tuple y=x;std::rotate(y.begin(),y.begin()+k%x.size(),y.end());return y;}
static uint64_t encode(const Tuple& x,int count,int n){uint64_t v=0;for(int j=0;j<count;++j)v=n*v+x[j];return v;}
static Tuple decode(uint64_t code,int count,int n){Tuple x(count);for(int j=count-1;j>=0;--j){x[j]=code%n;code/=n;}require(code==0,"vertex overflow");return x;}
static Tuple parse(const std::string& text){Tuple x;for(char c:text){auto j=alphabet.find(c);require(j!=std::string::npos,"invalid symbol");x.push_back(j);}return x;}

static std::vector<Parent> transport(const std::vector<Parent>& input,int m){
    std::vector<Parent> output;output.reserve(input.size()*m);
    for(const auto& row:input)for(int j=0;j<m;++j){
        auto y=row.x;
        if(row.deficit==2&&j==m-1){y.clear();y.push_back(row.x.back());y.insert(y.end(),row.x.begin(),row.x.end()-1);y.push_back(m);}
        else y.insert(y.begin()+j,m);
        output.push_back({std::move(y),row.deficit});
    }
    return output;
}

static std::vector<Tuple> transport_circles(const std::vector<Tuple>& input,int m){
    std::vector<Tuple> output;output.reserve(input.size()*(m-1));
    for(auto circle:input){
        for(auto& x:circle)if(x==m+1)x=m+2;
        for(int j=0;j<m-1;++j){auto y=circle;y.insert(y.begin()+j,m);auto least=std::min_element(y.begin(),y.end());std::rotate(y.begin(),least,y.end());output.push_back(std::move(y));}
    }
    auto sorted=output;std::sort(sorted.begin(),sorted.end());require(std::adjacent_find(sorted.begin(),sorted.end())==sorted.end(),"duplicate transported circle");
    return output;
}

struct Macro { Tuple base; uint8_t satellite; int visible; };
static Macro macro(const Parent& row,int variant,int m){
    int L=m-row.deficit;
    if(variant<m){auto x=row.x;x.insert(x.begin()+variant,m+1);return {std::move(x),uint8_t(m),L+(variant<L)};}
    auto x=rotate(row.x,L+variant-m);x.push_back(m);return {std::move(x),uint8_t(m+1),m+1};
}
static Tuple row_word(const Macro& row){
    Tuple out;int q=row.base.size();out.reserve((q+2)*row.visible+q-1);
    for(int j=0;j<row.visible;++j){auto x=rotate(row.base,j);if(j==0)out.insert(out.end(),x.begin(),x.end());else out.push_back(x.back());out.push_back(row.satellite);out.insert(out.end(),x.begin(),x.end());}
    require(out.size()==size_t((q+2)*row.visible+q-1),"row length mismatch");return out;
}

// Compute the maximum exact suffix-prefix overlap, including overlaps longer
// than a permutation. Only the suffix of the current output of length |next|
// can matter. The prefix function keeps this operation linear in input size.
static size_t overlap(const Tuple& tail,const Tuple& next){
    require(!next.empty()&&next.size()<=UINT32_MAX,"module exceeds overlap index range");
    std::vector<uint32_t> pi(next.size());
    for(size_t i=1,j=0;i<next.size();++i){while(j&&next[i]!=next[j])j=pi[j-1];if(next[i]==next[j])++j;pi[i]=j;}
    size_t matched=0,first=tail.size()>next.size()?tail.size()-next.size():0;
    for(size_t i=first;i<tail.size();++i){if(matched==next.size())matched=pi[matched-1];while(matched&&tail[i]!=next[matched])matched=pi[matched-1];if(tail[i]==next[matched])++matched;}
    return matched;
}

int main(int argc,char** argv){try{
    require(argc==5||argc==6,"usage: construct N INPUT.txt OUTPUT.txt RECIPE.json [ORDER.txt]");
    size_t parsed=0;int n=std::stoi(argv[1],&parsed);require(parsed==std::string(argv[1]).size(),"invalid degree");require(n>=11&&n<=13,"this release prepares degrees 11 through 13");
    auto begin=std::chrono::steady_clock::now();int m=9,h=n-3;std::ifstream input(argv[2]);require(bool(input),"cannot read input");
    std::string magic;
    input>>magic;require(magic=="CIRCLE4380V1","wrong input format");
    size_t row_count=0,circle_count=0;require(bool(input>>row_count>>circle_count),"truncated input counts");require(row_count==40320&&circle_count==357,"wrong input counts");
    std::vector<Parent> parents;parents.reserve(row_count);std::vector<Tuple> circles;
    for(size_t i=0;i<row_count;++i){std::string x;int d=0;require(bool(input>>x>>d),"truncated parent");auto y=parse(x);auto s=y;std::sort(s.begin(),s.end());require(s==Tuple({0,1,2,3,4,5,6,7,8})&&(d==0||d==2),"invalid parent");parents.push_back({std::move(y),d});}
    for(size_t i=0;i<circle_count;++i){std::string x;require(bool(input>>x),"truncated circle");auto y=parse(x);require(y.size()==8,"invalid circle length");auto sorted=y;std::sort(sorted.begin(),sorted.end());require(std::adjacent_find(sorted.begin(),sorted.end())==sorted.end()&&sorted.back()<=10&&std::find(sorted.begin(),sorted.end(),9)==sorted.end(),"invalid circle alphabet");circles.push_back(std::move(y));}
    require(bool(input),"truncated input");require(!(input>>magic),"trailing input");
    while(m<n-2){parents=transport(parents,m);circles=transport_circles(circles,m);++m;}
    uint64_t charge=0;for(const auto& p:parents)charge+=p.deficit;
    require(parents.size()==factorial(m-1),"parent count mismatch");
    uint64_t macro_count=m*parents.size()+charge;
    std::vector<Edge> edges;edges.reserve(macro_count+h*circles.size());std::vector<uint64_t> keys;keys.reserve(edges.capacity());
    uint64_t classes=0,row_cost=0;
    for(uint32_t p=0;p<parents.size();++p)for(int v=0;v<m+parents[p].deficit;++v){
        auto r=macro(parents[p],v,m);auto a=encode(r.base,h,n),b=encode(rotate(r.base,r.visible+1),h,n);
        edges.push_back({a,b,p,none,uint16_t(v),0});keys.push_back(a);classes+=r.visible;row_cost+=(n+1)*r.visible+1;
    }
    require(edges.size()==macro_count&&classes==factorial(n-1),"completion ledger mismatch");
    for(uint32_t c=0;c<circles.size();++c)for(int j=0;j<h;++j){auto a=encode(rotate(circles[c],j),h,n),b=encode(rotate(circles[c],j+1),h,n);edges.push_back({a,b,c,none,uint16_t(j),1});keys.push_back(a);}
    std::sort(keys.begin(),keys.end());keys.erase(std::unique(keys.begin(),keys.end()),keys.end());require(keys.size()<none,"too many vertices");
    auto vertex=[&](uint64_t key){auto it=std::lower_bound(keys.begin(),keys.end(),key);require(it!=keys.end()&&*it==key,"unbalanced endpoint set");return uint32_t(it-keys.begin());};
    std::vector<uint32_t> adj(keys.size(),none),degree(keys.size()),indegree(keys.size());DSU dsu(keys.size());
    for(uint32_t e=0;e<edges.size();++e){auto& edge=edges[e];edge.head=vertex(edge.head);edge.tail=vertex(edge.tail);edge.next=adj[edge.head];adj[edge.head]=e;++degree[edge.head];++indegree[edge.tail];dsu.join(edge.head,edge.tail);}
    require(degree==indegree,"literal graph is unbalanced");
    std::vector<uint32_t> cut(keys.size(),none),cut_length(keys.size());
    for(uint32_t e=macro_count;e<edges.size();++e){auto& first=edges[e];if(degree[first.head]==1)continue;uint32_t at=e,length=0;
        do{++length;auto tail=edges[at].tail;if(degree[tail]!=1)break;at=adj[tail];require(edges[at].connector,"connector arc passed a row");require(length<=edges.size(),"closed connector-only component");}while(true);
        auto root=dsu.find(first.head);if(length>cut_length[root]){cut[root]=e;cut_length[root]=length;}
    }
    std::vector<uint32_t> roots;for(uint32_t v=0;v<keys.size();++v)if(dsu.find(v)==v){require(cut[v]!=none,"module lacks a safe connector cut");roots.push_back(v);}
    std::vector<uint32_t> prescribed_order;
    if(argc==6){
        std::ifstream prescribed(argv[5]);require(bool(prescribed),"cannot read module order");
        std::vector<uint8_t> seen(roots.size());std::string token;
        while(prescribed>>token){
            require(!token.empty(),"empty module ID");uint64_t id=0;
            for(char c:token){require(c>='0'&&c<='9',"invalid module ID");require(id<=UINT64_MAX/10,"module ID overflow");id*=10;require(id<=UINT64_MAX-uint64_t(c-'0'),"module ID overflow");id+=uint64_t(c-'0');}
            require(id<roots.size()&&!seen[id],"invalid or duplicate module ID");seen[id]=1;prescribed_order.push_back(uint32_t(id));
        }
        require(prescribed.eof()&&prescribed_order.size()==roots.size(),"incomplete or malformed module order");
    }
    std::vector<uint8_t> removed(edges.size());uint64_t removed_count=0;
    std::string spool_path=std::string(argv[3])+".modules.tmp";std::ofstream spool(spool_path,std::ios::binary|std::ios::trunc);require(bool(spool),"cannot create module spool");
    std::vector<Piece> pieces;uint64_t spool_size=0,used=0,max_piece=0;
    for(auto root:roots){uint32_t edge=cut[root],start=none,end=edges[edge].head;
        for(uint32_t j=0;j<cut_length[root];++j){removed[edge]=1;++removed_count;start=edges[edge].tail;if(j+1<cut_length[root])edge=adj[start];}
        std::vector<uint32_t> stack,order;uint32_t at=start;
        while(true){while(adj[at]!=none&&removed[adj[at]])adj[at]=edges[adj[at]].next;
            if(adj[at]!=none){auto e=adj[at];adj[at]=edges[e].next;stack.push_back(e);at=edges[e].tail;}
            else{if(stack.empty())break;auto e=stack.back();stack.pop_back();order.push_back(e);at=edges[e].head;}
        }
        std::reverse(order.begin(),order.end());auto word=decode(keys[start],h,n);at=start;uint64_t predicted=h;
        for(auto e:order){auto& r=edges[e];require(r.head==at&&!removed[e]&&dsu.find(r.head)==root,"Euler path mismatch");Tuple payload;
            if(r.connector){payload=rotate(circles[r.source],r.variant);payload.push_back(payload[0]);predicted+=1;}
            else{auto d=macro(parents[r.source],r.variant,m);payload=row_word(d);predicted+=(n+1)*d.visible+1;}
            require(std::equal(word.end()-h,word.end(),payload.begin()),"literal row join mismatch");word.insert(word.end(),payload.begin()+h,payload.end());at=r.tail;++used;
        }
        require(at==end&&word.size()==predicted,"opened module mismatch");
        Piece p{spool_size,word.size(),root,cut_length[root],Tuple(word.begin(),word.begin()+n-1),Tuple(word.end()-n+1,word.end())};
        spool.write(reinterpret_cast<char*>(word.data()),word.size());require(bool(spool),"module write failed");spool_size+=word.size();max_piece=std::max(max_piece,uint64_t(word.size()));pieces.push_back(std::move(p));
    }
    require(used+removed_count==edges.size(),"not all edges used");spool.close();
    uint64_t raw_ledger=row_cost+h*circles.size()+h*pieces.size()-removed_count;require(spool_size==raw_ledger,"module ledger mismatch");
    // Every part already contains all its assigned rows. Reordering parts and
    // taking any exact overlap therefore preserves those rows literally.
    std::vector<uint32_t> order;std::vector<uint8_t> chosen(pieces.size());uint32_t next=0;
    if(argc==6)order=std::move(prescribed_order);
    while(order.size()<pieces.size()){chosen[next]=1;order.push_back(next);int best=-1;uint32_t following=none;
        for(uint32_t j=0;j<pieces.size();++j)if(!chosen[j]){int score=0;for(int k=n-1;k>0;--k)if(std::equal(pieces[next].suffix.end()-k,pieces[next].suffix.end(),pieces[j].prefix.begin())){score=k;break;}if(score>best){best=score;following=j;}}
        next=following;
    }
    std::ifstream parts(spool_path,std::ios::binary);std::ofstream output(argv[3],std::ios::binary|std::ios::trunc);require(bool(output),"cannot create output");
    Tuple tail;uint64_t length=0,saved=0;std::vector<size_t> joins;
    for(auto i:order){const auto& piece=pieces[i];Tuple word(piece.length);parts.seekg(piece.offset);parts.read(reinterpret_cast<char*>(word.data()),word.size());require(bool(parts),"cannot read module");auto overlap_length=tail.empty()?0:overlap(tail,word);joins.push_back(overlap_length);saved+=overlap_length;
        std::string text; text.reserve(word.size()-overlap_length);for(size_t j=overlap_length;j<word.size();++j)text.push_back(alphabet[word[j]]);output.write(text.data(),text.size());length+=text.size();
        tail.insert(tail.end(),word.begin()+overlap_length,word.end());if(tail.size()>max_piece)tail.erase(tail.begin(),tail.end()-max_piece);
    }
    output.put('\n');output.close();require(bool(output)&&length==raw_ledger-saved,"final length ledger mismatch");
    double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count();
    std::ofstream recipe(argv[4]);recipe<<"{\"n\":"<<n<<",\"alphabet\":\""<<alphabet.substr(0,n)<<"\",\"parent_rows\":"<<parents.size()<<",\"charge\":"<<charge<<",\"macro_rows\":"<<macro_count<<",\"visible_classes\":"<<classes<<",\"circles\":"<<circles.size()<<",\"modules\":"<<pieces.size()<<",\"removed_connector_edges\":"<<removed_count<<",\"row_cost\":"<<row_cost<<",\"module_sum_length\":"<<raw_ledger<<",\"overlap_saved\":"<<saved<<",\"length\":"<<length<<",\"construction_seconds\":"<<seconds<<",\"maximum_module_length\":"<<max_piece<<",\"module_order\":[";
    for(size_t j=0;j<order.size();++j){if(j)recipe<<',';recipe<<order[j];}recipe<<"],\"overlaps\":[";for(size_t j=0;j<joins.size();++j){if(j)recipe<<',';recipe<<joins[j];}recipe<<"]}\n";recipe.close();require(bool(recipe),"recipe write failed");
    std::remove(spool_path.c_str());
    std::cout<<"{\"n\":"<<n<<",\"length\":"<<length<<",\"modules\":"<<pieces.size()<<",\"removed_connector_edges\":"<<removed_count<<",\"overlap_saved\":"<<saved<<",\"construction_seconds\":"<<seconds<<"}\n";
    return 0;
}catch(const std::exception& e){std::cerr<<e.what()<<'\n';return 2;}}
