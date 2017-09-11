#include <iostream>
#include <stdio.h>
#include <stdlib.h>
#include <vector>
#include <list>
#include <string>
#include <numeric>
#include <utility>
#include <stack>
#include <climits>
#include <algorithm>

#define MAX_DEPTH 3
#define DEPTH 4
#define ENDGAMECUTOFF 7
#define ENDGAMEFLAT 800
#define TOPFLAT 700
#define WTOPFLAT 0
#define WTOPSTAND 100
#define WTOPCAP 250
#define WSTACKFLATADD 100
#define WSTACKSTANDADD 200
#define WSTACKCAPADD 400
#define WSTACKFLATSUB 200
#define WSTACKSTANDSUB 200
#define WSTACKCAPSUB 300
#define WTHREAT4 2500
#define WTHREAT3 800
#define WH0 0
#define WH1 0
#define WH2 800
#define WH3 1300
#define WV0 0
#define WV1 0
#define WV2 800
#define WV3 1300

using namespace std;

float weights[] = {354.974,
                  -109.588,
                  118.397,
                  -67.5213,
                  270.4,
                  -229.6,
                  136.096,
                  -17.7546,
                  202.1,
                  -187.502,
                  427.098,
                  -33.2461,
                  263.949,
                  -190.3,
                  219.698,
                  -196.7,
                  350.969,
                  -287.503,
                  121.374,
                  27.7831,
                  819.3,
                  1305.4,
                  1500,
                  4000,
                  8000,
                  147.653,
                  16.8829,
                  -795.8,
                  -1299.7,
                  -1500,
                  4000,
                  8000,
                  10000};//influence};};

class Player{
  public:
    int flats;
    int capstones;
    Player(int,int);
    Player();
    Player(Player*);
};

Player::Player(){

}

Player::Player(int flats, int capstones){
  this->flats = flats;
  this->capstones = capstones;
}

Player::Player(Player* p)
{
  this->flats = p->flats;
  this->capstones = p->capstones;
}

class Board{
  public:
    Board();
    Board(int);
    Board(Board*);
    int n;
    int total_squares;
    vector< vector< pair<int,char> > > b;
    int turn;
    int max_movable;
    int max_down;
    int max_up;
    int max_flats;
    int max_capstones;
    char max_left;
    char max_right;
    int moves;
    int miniMaxVal;
    vector<Player> pl;
    vector<string> all_squares;
    int square_to_num(string);
    string square_to_string(int);
    void execute_move(string);
    vector<vector<int>> partition(int);
    bool check_valid(int,char,vector<int>);
    vector<string> generate_stack_moves(int);
    vector<string> generate_all_moves(int);
    int evaluate_board(int);
    Board board_after_move(string);
    bool check_road_win(int);
    bool check_road_win(int,char);
    int check_flat_win();
    vector<int> get_neighbours(int);
    bool isTerminalState(int);
    vector<pair<int,int> > getGroups(int);
    int weightStonesAndStack(int);
    int numEmptyBlocks();
    vector<int> getFeatureVector(int);
    int getInfluence(int);
};

int Board::numEmptyBlocks(){
  int e = 0;
  for(int i = 0; i<total_squares; i++){
    if(b[i].size() == 0)
      e++;
  }
  return e;
}

int Board::getInfluence(int player)
{
  unsigned int inf[] = {0,0};
  unsigned int ul0 = 0;
  unsigned int maskX0 = 0, maskY0 = 0, maskX1 = 0, maskY1 = 0;
  for(int i=0; i<total_squares; i++)
  {
    int bSize = b[i].size();
    if(bSize>0)
    {
      inf[b[i][bSize-1].first] = inf[b[i][bSize-1].first] | (1<<i);
    }
    unsigned int bit = 1<<i;
    if(i%n > 0)
      maskX0 = maskX0 | bit;
    if(i/n > 0)
      maskY0 = maskY0 | bit;
    if(i%n < n-1)
      maskX1 = maskX1 | bit;
    if(i/n < n-1)
      maskY1 = maskY1 | bit;
  }

  unsigned int expanded0, expanded1, intersect;
  while(true)
  {
    expanded0 = inf[0] | ((inf[0] & maskX0)>>1) | ((inf[0] & maskX1)<<1) | ((inf[0] & maskY0)>>n) | ((inf[0] & maskY1)<<n);
    expanded1 = inf[1] | ((inf[1] & maskX0)>>1) | ((inf[1] & maskX1)<<1) | ((inf[1] & maskY0)>>n) | ((inf[1] & maskY1)<<n);

    intersect = expanded0 & expanded1;
    expanded0 = expanded0 & ~intersect;
    expanded1 = expanded1 & ~intersect;

    if((expanded0 & ~inf[0]) != ul0 || (expanded1 & ~inf[1]) != ul0)
    {
      inf[0] = inf[0] | expanded0;
      inf[1] = inf[1] | expanded1;
    }
    else
      break;
  }
  int count0 = 0, count1 = 0;
  for(int i=0; i<total_squares; i++, inf[0]>>=1, inf[1]>>=1)
  {
    if((inf[0] & 1) == 1)
      count0++;
    if((inf[1] & 1) == 1)
      count1++;
  }
  if(player == 0)
    return (count0 - count1);
  return (count1 - count0);

}

vector< pair<int,int> > Board::getGroups(int player) {
  vector< pair<int,int> > ret;
  bool visited[total_squares];

  for(int i=0; i<total_squares; i++)
    visited[i]=false;

  for(int i=0; i<total_squares; i++)
  {
    bool found=false;
    int maxRow=i/n;
    int minRow=i/n;
    int maxCol=i%n;
    int minCol=i%n;

    if(b[i].size()>0 && b[i][b[i].size()-1].first==player && b[i][b[i].size()-1].second!='S' && !visited[i])
    {
      found=true;
      vector<int> curr_neighbours=get_neighbours(i);
      list<int> rec_queue;

      for(int j=0; j<curr_neighbours.size(); j++)
      {
        if(b[curr_neighbours[j]].size()>0 && b[curr_neighbours[j]][b[curr_neighbours[j]].size()-1].first==player && b[curr_neighbours[j]][b[curr_neighbours[j]].size()-1].second!='S' && !visited[curr_neighbours[j]])
        {
          rec_queue.push_back(curr_neighbours[j]);
        }
      }
      visited[i]=true;
      while(!rec_queue.empty())
      {
        int curr_cell=rec_queue.front();
        rec_queue.pop_front();
        curr_neighbours=get_neighbours(curr_cell);
        for(int j=0; j<curr_neighbours.size(); j++)
        {
          if(b[curr_neighbours[j]].size()>0 && b[curr_neighbours[j]][b[curr_neighbours[j]].size()-1].first==player && b[curr_neighbours[j]][b[curr_neighbours[j]].size()-1].second!='S' && !visited[curr_neighbours[j]])
          {
            rec_queue.push_back(curr_neighbours[j]);
          }
        }
        int curr_row=curr_cell/n;
        int curr_col=curr_cell%n;
        if(curr_row>maxRow)
          maxRow=curr_row;
        if(curr_row<minRow)
          minRow=curr_row;
        if(curr_col>maxCol)
          maxCol=curr_col;
        if(curr_col<minCol)
          minCol=curr_col;
        visited[curr_cell]=true;
      }
    }
    else
    {
      visited[i]=true;
    }

    if(found)
    {
      pair<int,int> temp(maxRow-minRow+1,maxCol-minCol+1);
      ret.push_back(temp);
    }

  }
  if(ret.size()==0)
  {
    pair<int,int> temp(0,0);
    ret.push_back(temp);
  }
  return ret;
}

int Board::weightStonesAndStack(int player)
{
  int sum=0;
  int endGameCutoff=ENDGAMECUTOFF, endGameFlat=ENDGAMEFLAT, topFlat=TOPFLAT;
  int wTopFlat=WTOPFLAT, wTopStand=WTOPSTAND, wTopCap=WTOPCAP;
  int wStackFlatAdd=WSTACKFLATADD, wStackStandAdd=WSTACKSTANDADD, wStackCapAdd=WSTACKCAPADD;
  int wStackFlatSub=WSTACKFLATSUB, wStackStandSub=WSTACKSTANDSUB, wStackCapSub=WSTACKCAPSUB;

  int remainingFLats = min(pl[0].flats, pl[1].flats);
  if(remainingFLats>endGameCutoff)
    remainingFLats=endGameCutoff;

  wTopFlat = topFlat + (endGameCutoff - remainingFLats) * endGameFlat / endGameCutoff;

  for(int i=0; i<total_squares; i++)
  {
    if(b[i].size()>0)
    {
      int bSize=b[i].size();
      int topColour=b[i][bSize-1].first;
      char topType=b[i][bSize-1].second;
      if(topColour==player && topType == 'F')
        sum+=wTopFlat;
      else if(topColour==player && topType=='S')
        sum+=wTopStand;
      else if(topColour==player && topType=='C')
        sum+=wTopCap;
      else if(topColour!=player && topType=='F')
        sum-=wTopFlat;
      else if(topColour!=player && topType=='S')
        sum-=wTopStand;
      else if(topColour!=player && topType=='C')
        sum-=wTopCap;
      for(int j=0; j<bSize-1; j++)
      {
        if(topColour==player)
        {
          if(b[i][j].first==topColour && topType=='F')
            sum+=wStackFlatAdd;
          else if(b[i][j].first==topColour && topType=='S')
            sum+=wStackStandAdd;
          else if(b[i][j].first==topColour && topType=='C')
            sum+=wStackCapAdd;
          else if(b[i][j].first != topColour && topType=='F')
            sum-=wStackFlatAdd;
          else if(b[i][j].first != topColour && topType=='S')
            sum-=wStackStandAdd;
          else if(b[i][j].first != topColour && topType=='C')
            sum-=wStackCapAdd;

        }
        else {
          if(b[i][j].first == topColour && topType=='F')
            sum-=wStackFlatSub;
          else if(b[i][j].first == topColour && topType=='S')
            sum-=wStackStandSub;
          else if(b[i][j].first == topColour && topType=='C')
            sum-=wStackCapSub;
          else if(b[i][j].first != topColour && topType=='F')
            sum+=wStackFlatSub;
          else if(b[i][j].first != topColour && topType=='S')
            sum+=wStackStandSub;
          else if(b[i][j].first != topColour && topType=='C')
            sum+=wStackCapSub;
        }
      }
    }
  }
  return sum;
}

bool Board::check_road_win(int player){
  return check_road_win(player,'h') || check_road_win(player,'v');
}

bool Board::check_road_win(int player,char dir){
  vector<bool> visited(total_squares, false);
  vector<bool> final_positions(total_squares, false);

  stack<int> dfs_stack;

  if(dir == 'v'){
    for(int i=0; i<n; i++){
      int size_st = b[i].size();
      if(size_st > 0 && b[i][size_st-1].first == player && b[i][size_st-1].second != 'S'){
        visited[i] = true;
        dfs_stack.push(i);
      }
      final_positions[total_squares-1-i] = true;
    }
  }
  else if(dir == 'h'){
    for(int i=0; i<n; i++){
      int size_st = b[i*n].size();
      if(size_st > 0 && b[i*n][size_st-1].first == player && b[i*n][size_st-1].second != 'S'){
        visited[i*n] = true;
        dfs_stack.push(i*n);
      }
      final_positions[(i+1)*n-1] = true;
    }
  }

  while(dfs_stack.size() > 0){
    int temp_cell = dfs_stack.top();
    dfs_stack.pop();

    if(final_positions[temp_cell])
      return true;


    vector<int> neighbour = get_neighbours(temp_cell);
    for(int j=0; j<neighbour.size(); j++){
      int curr_neighbour = neighbour[j];
      int temp_cell_size = b[curr_neighbour].size();

      if(!visited[curr_neighbour] && temp_cell_size > 0 && b[curr_neighbour][temp_cell_size-1].first == player && b[curr_neighbour][temp_cell_size-1].second != 'S'){

        dfs_stack.push(curr_neighbour);
        visited[curr_neighbour] = true;
      }

    }
  }
  return false;
}

int Board::check_flat_win(){
  int count_1 = 0;
  int count_2 = 0;
  for(int i=0; i<total_squares; i++){
    int size = b[i].size();
    if(size > 0 && b[i][size-1].first == 0 && b[i][size-1].second != 'S')
      count_1++;
    if(size > 0 && b[i][size-1].first == 1 && b[i][size-1].second != 'S')
      count_2++;
  }

  if(count_1 > count_2)
    return 0;
  else if(count_2 > count_1)
    return 1;
  else if(pl[0].flats == 0)
    return 1;
  else if(pl[1].flats == 0)
    return 0;
  else       //ADDED_SOMETHING
    return 0;
}

bool Board::isTerminalState(int player){
  bool allSquaresFilled = true;
  for(int i=0; i<total_squares; i++)
  {
    if(b[i].size()==0)
    {
      allSquaresFilled = false;
      break;
    }
  }

  if(pl[0].flats > 0 && pl[1].flats > 0 && !allSquaresFilled)
    return check_road_win(player);
  else
    return (check_flat_win() == player);

}

vector<int> Board::get_neighbours(int cell){
  vector<int> neighbours;
  if(cell < 0 || cell >= total_squares){
    return neighbours;
  }
  else if(cell == 0){
    neighbours.push_back(cell+1);
    neighbours.push_back(cell+n);
    return neighbours;
  }
  else if(cell == n-1){
    neighbours.push_back(cell-1);
    neighbours.push_back(cell+n);
    return neighbours;
  }
  else if(cell == total_squares-n){
    neighbours.push_back(cell+1);
    neighbours.push_back(cell-n);
    return neighbours;
  }
  else if(cell == total_squares-1){
    neighbours.push_back(cell-1);
    neighbours.push_back(cell-n);
    return neighbours;
  }
  else if(cell < n){
    neighbours.push_back(cell-1);
    neighbours.push_back(cell+1);
    neighbours.push_back(cell+n);
    return neighbours;
  }
  else if(cell % n == 0){
    neighbours.push_back(cell+1);
    neighbours.push_back(cell-n);
    neighbours.push_back(cell+n);
    return neighbours;
  }
  else if((cell+1) % n == 0){
    neighbours.push_back(cell-1);
    neighbours.push_back(cell-n);
    neighbours.push_back(cell+n);
    return neighbours;
  }
  else if(cell > total_squares-n){
    neighbours.push_back(cell-1);
    neighbours.push_back(cell+1);
    neighbours.push_back(cell-n);
    return neighbours;
  }
  else{
    neighbours.push_back(cell-1);
    neighbours.push_back(cell+1);
    neighbours.push_back(cell-n);
    neighbours.push_back(cell+n);
    return neighbours;
  }
}

Board::Board(){}

Board::Board(Board* obj){
  this->n = obj->n;
  this->total_squares = obj->total_squares;
  int sz = (obj->b).size();
  for(int i=0; i<sz; i++)
    b.push_back(obj->b[i]);

  this->turn = obj->turn;
  this->max_movable = obj->max_movable;
  this->max_down = obj->max_down;
  this->max_up = obj->max_up;
  this->max_flats = obj->max_flats;
  this->max_capstones = obj->max_capstones;
  this->max_left = obj->max_left;
  this->max_right = obj->max_right;
  this->moves = obj->moves;

  sz = (obj->pl).size();
  for(int i=0; i<sz; i++)
  {
    pl.push_back(Player(obj->pl[i].flats, obj->pl[i].capstones));
  }
  sz = (obj->all_squares).size();
  for(int i=0; i<sz; i++)
    all_squares.push_back(obj->all_squares[i]);
  this->miniMaxVal = obj->miniMaxVal;
}

Board::Board(int n){
  this->n = n;
  this->total_squares = n*n;
  b.resize(total_squares);
  this->turn = 0;
  if(n == 5){
    this->max_flats = 21;
    this->max_capstones = 1;
  }
  else if(n == 6){
    this->max_flats = 30;
    this->max_capstones = 1;
  }
  else if(n == 7){
    this->max_flats = 40;
    this->max_capstones = 1;
  }
  this->max_movable = n;
  this->max_down = 1;
  this->max_up = n;
  this->max_left = 'a';
  this->max_right = (char)((int)('a') + n - 1);
  this->moves = 0;

  pl.push_back(Player(this->max_flats, this->max_capstones));
  pl.push_back(Player(this->max_flats, this->max_capstones));

  for(int i=0; i<this->total_squares; i++){
    all_squares.push_back(this->square_to_string(i));
  }

  this->miniMaxVal = 0;
}

int Board::square_to_num(string s){
  int row = (int)(s[0])-96;
  int col = (int)(s[1]) - 48;
  return this->n *(col-1) + (row-1);
}

vector<int> Board::getFeatureVector(int player)
{
  vector<int> ret(32, 0);

  for(int i=0; i<total_squares; i++)
  {
    if(b[i].size()>0)
    {
      int bSize=b[i].size();
      int topColour=b[i][bSize-1].first;
      char topType=b[i][bSize-1].second;
      if(topColour==player && topType == 'F')
        ret[0]++;
      else if(topColour==player && topType=='S')
        ret[2]++;
      else if(topColour==player && topType=='C')
        ret[4]++;
      else if(topColour!=player && topType=='F')
        ret[1]++;
      else if(topColour!=player && topType=='S')
        ret[3]++;
      else if(topColour!=player && topType=='C')
        ret[5]++;
      for(int j=0; j<bSize-1; j++)
      {
        if(topColour==player)
        {
          if(b[i][j].first==topColour && topType=='F')
            ret[6]++;
          else if(b[i][j].first==topColour && topType=='S')
            ret[8]++;
          else if(b[i][j].first==topColour && topType=='C')
            ret[10]++;
          else if(b[i][j].first != topColour && topType=='F')
            ret[7]++;
          else if(b[i][j].first != topColour && topType=='S')
            ret[9]++;
          else if(b[i][j].first != topColour && topType=='C')
            ret[11]++;

        }
        else {
          if(b[i][j].first == topColour && topType=='F')
            ret[13]++;
          else if(b[i][j].first == topColour && topType=='S')
            ret[15]++;
          else if(b[i][j].first == topColour && topType=='C')
            ret[17]++;
          else if(b[i][j].first != topColour && topType=='F')
            ret[12]++;
          else if(b[i][j].first != topColour && topType=='S')
            ret[14]++;
          else if(b[i][j].first != topColour && topType=='C')
            ret[16]++;
        }
      }
    }
  }

  vector< pair<int,int> > gr = getGroups(player);
  int sz = gr.size();
  for(int i=0; i<sz; i++)
  {
    ret[17+gr[i].first]++;
    ret[17+gr[i].second]++;
  }

  gr = getGroups(1-player);
  sz = gr.size();
  for(int i=0; i<sz; i++)
  {
    ret[24+gr[i].first]++;
    ret[24+gr[i].second]++;
  }

  return ret;
}


int Board::evaluate_board(int player){
  // return rand()%50;
  if(isTerminalState(1-player)){
    return -INT_MAX;
  }

  float ret = 0;
  vector<int> fVector = getFeatureVector(player);
  int sz = fVector.size();
  for(int i=0; i<sz; i++)
  {
    ret += fVector[i]*weights[i];
  }
  return (int)ret;
}

string Board::square_to_string(int s){
  int row = s % this->n;
  int col = s/this->n;
  char r = (char)(row+97);
  char c = (char)(col+49);
  string ret;
  ret = string() + r + c;
  return ret;
}

Board Board::board_after_move(string move_string){
  Board nBoard = Board(this);

  nBoard.execute_move(move_string);
  return nBoard;
}

void Board::execute_move(string move_string){
  int current_piece = 0;
  if(this->turn == 0)
    this->moves = this->moves + 1;
  if(this->moves != 1)
    current_piece = this->turn;
  else
    current_piece = 1 - this->turn;

  if(isalpha(move_string[0])){
    //std::cerr << "Start Exec" << std::endl;
    int cell = this->square_to_num(move_string.substr(1));
    if(move_string[0] == 'F' || move_string[0] == 'S'){
      b[cell].push_back(make_pair(current_piece,move_string[0]));
      //std::cerr << "Pushed " << move_string << std::endl;
      pl[current_piece].flats = pl[current_piece].flats - 1;
    }
    else if(move_string[0] == 'C'){
      this->b[cell].push_back(make_pair(current_piece,move_string[0]));
      pl[current_piece].capstones = pl[current_piece].capstones - 1;
    }
  }
  else if(isdigit(move_string[0])){   //ERROR_HERE  //1e3+1
    int change = 0;
    int count = (int)move_string[0] - 48;    //count=1
    int cell = this->square_to_num(move_string.substr(1,3));  //cell=14
    char direction = move_string[3]; //dir='+'
    if(direction == '+')
      change = this->n;          //change=5
    else if(direction == '-')
      change = - this->n;
    else if(direction == '>')
      change = 1;
    else if(direction == '<')
      change = -1;

    int prev_cell = cell;    //prev_cell=14
    int len = move_string.length(); //len=5
    for(int i=4; i<len; i++){

      int next_count = int(move_string[i]) - 48; //next_count=1
      int next_cell = prev_cell + change; //next_cell=19
      int last = this->b[next_cell].size(); //last=0
      if(last > 0 && (this->b[next_cell][last-1]).second == 'S')
        this->b[next_cell][last-1] = make_pair(this->b[next_cell][last-1].first , 'F');
      if(next_count == count){
        vector<pair<int,char>> ins;
        int lCell = this->b[cell].size(); //lCell=1

        for(int j=lCell-count; j<lCell; j++)
          ins.push_back(this->b[cell][j]);

        this->b[next_cell].insert(this->b[next_cell].end(), ins.begin(), ins.end());  //1S
      }
      else{
        vector<pair<int,char>> ins;
        int lCell = this->b[cell].size(); //lCell=2

        for(int j=lCell-count; j<(lCell-count+next_count); j++)  //changedHERE
          ins.push_back(this->b[cell][j]);

        this->b[next_cell].insert(this->b[next_cell].end(), ins.begin(), ins.end());
      }
      prev_cell = next_cell; //prev_cell=19
      count = count - next_count; //count=0

    }

    count = (int)move_string[0] - 48; //count=1
    int l = this->b[cell].size(); //l=1
    //std::cerr << "LbeforeDELETING" << l << std::endl;
    this->b[cell].erase(this->b[cell].end()-count, this->b[cell].end());  ///check this statement for errors
    //std::cerr << "LafterDELETING" << this->b[cell].size() << std::endl;
  }

  this->turn = 1 - this->turn;
}

vector<vector<int>> Board::partition(int n){          //Check this function
  vector<vector<int>> ls;
  vector<int> single;
  single.push_back(n);
  ls.push_back(single);
  for(int i=1; i<=n-1; i++){
    vector<vector<int>> temp = this->partition(n-i);
    int sizeVec = temp.size();
    for(int j=0; j<sizeVec; j++){
      vector<int> tempL;
      tempL.push_back(i);
      tempL.insert(tempL.end(),temp[j].begin(),temp[j].end());
      ls.push_back(tempL);
    }
  }
  return ls;
}

bool Board::check_valid(int cell, char direction, vector<int> partition){
  int change = 0;
  if(direction == '+')
    change = this->n;
  else if(direction == '-')
    change = - this->n;
  else if(direction == '>')
    change = 1;
  else if(direction == '<')
    change = -1;

  int pSize = partition.size();
  for(int i=0; i<pSize; i++){
    int next_cell = cell + change*(i+1);
    int sizeNext = this->b[next_cell].size();
    if(sizeNext > 0 && this->b[next_cell][sizeNext-1].second == 'C')
      return false;
    else if(sizeNext > 0 && this->b[next_cell][sizeNext-1].second == 'S' && i != (pSize-1))
      return false;
    else if(i == pSize-1 && sizeNext > 0 && this->b[next_cell][sizeNext-1].second == 'S' && partition[i] > 1)
      return false;
    else if(i == pSize-1 && sizeNext > 0 && this->b[next_cell][sizeNext-1].second == 'S' && this->b[cell][this->b[cell].size()-1].second != 'C')
      return false;
  }
  return true;
}

vector<string> Board::generate_stack_moves(int cell){
  vector<string> all_moves;
  int r = cell % this->n;
  int c = cell/this->n;
  int sizeSt = this->b[cell].size();
  char dirs[4] = {'+','-','<','>'};

  int up = this->n - 1 - c;
  int down = c;
  int right = this->n - 1 - r;
  int left = r;
  int rem_squares[4] = {up,down,left,right};

  int l = min(sizeSt,this->n);
  //std::cerr << "GENStackMoves" << l << " " << cell << std::endl;

  for(int num=0; num<l; num++){
    vector<vector<int>> part_list = this->partition(num+1);
    for(int di=0; di<4; di++){
      vector<vector<int>> part_dir;
      int part_size = part_list.size();
      for(int a=0; a<part_size; a++){
        if(part_list[a].size() <= rem_squares[di])
          part_dir.push_back(part_list[a]);
      }

      part_size = part_dir.size();
      for(int a=0; a<part_size; a++){
        if(this->check_valid(cell,dirs[di],part_dir[a])){
          string part_string = "";
          int sizeP = part_dir[a].size();
          for(int j=0; j<sizeP; j++){
            part_string = part_string + to_string(part_dir[a][j]);   //
          }
          int sum_of_elems = std::accumulate(part_dir[a].begin(), part_dir[a].end(), 0);
          all_moves.push_back(to_string(sum_of_elems) + all_squares[cell] + dirs[di] + part_string); //initialize all_squares
        }
      }
    }
  }
  return all_moves;
}

vector<string> Board::generate_all_moves(int player){   ///REQUIRE PLAYER CLASS??
  vector<string> all_moves;

  for(int i=0; i<this->total_squares; i++){
    if(this->b[i].size() == 0){
      if(this->pl[player].flats > 0)
        all_moves.push_back('F' + this->all_squares[i]);
      if(this->moves != player && this->pl[player].flats > 0)
        all_moves.push_back('S' + this->all_squares[i]);
      if(this->moves != player && this->pl[player].capstones > 0)
        all_moves.push_back('C' + this->all_squares[i]);
    }
  }

  if(this->moves != player){
    for(int i=0; i<this->total_squares; i++){
      int l = this->b[i].size();
      if(l > 0 && this->b[i][l-1].first == player){
        //std::cerr << "STACKLOC"  << i  << " " << l << std::endl;
        vector<string> stMoves = this->generate_stack_moves(i);
        all_moves.insert(all_moves.end(),stMoves.begin(),stMoves.end());
      }
    }
  }
  random_shuffle(all_moves.begin(), all_moves.end());

  return all_moves;
}

class MadanPlayer{
  public:
    int player;
    int time_left;
    int n;
    Board game;
    MadanPlayer();
    void play();
    int t_start;
    int total_time;
    string ABMinMax(Board* ,int);
    string ABMaxMove(Board*, string, int, int, int, int);
    string ABMinMove(Board*, string, int, int, int, int);
};

int univ_count = 0;

MadanPlayer::MadanPlayer(){
  string inp_pl;
  string inp_n;
  string inp_ti;
  cin >> inp_pl;
  cin >> inp_n;
  cin >> inp_ti;
  //std::cerr << inp_pl << inp_n << inp_ti << std::endl;
  //int space1=inp.find_first_of(" ",0);
  //int space2=inp.find_first_of(" ", space1+1);
  //this->player=atoi(inp.substr(0,space1).c_str());
  //this->n=atoi(inp.substr(space1+1, space2-space1-1).c_str());
  //this->time_left=atoi(inp.substr(space2+1, inp.size()-space2-1).c_str());
  this->player = atoi(inp_pl.c_str())-1;
  this->n = atoi(inp_n.c_str());
  this->time_left = atoi(inp_ti.c_str());
  this->t_start = time(0);
  this->total_time = this->time_left;
  game=Board(n);
  this->play();
}

void MadanPlayer::play()
{
  int t_moveStart = 0;
  string oppMove;
  bool firstMove = true;

  if(this->player == 1)
  {
    //std::cerr << "HERE" << std::endl;
    string move;
    cin>>move;
    oppMove = move;
    this->game.execute_move(move);
  }

  while(true)
  {
    string move = "";

    t_start = time(0);

    vector<string> all_moves = this->game.generate_all_moves(this->player);
    int sz = all_moves.size();

    std::cerr << "Time Left: " << time_left << std::endl;
    std::cerr << "Branching Factor: " << sz << std::endl;

    //std::cerr << t_aim << std::endl;

    // if(time_left < 0.10*total_time){
    //   move = this->ABMinMax(&game, 2);
    // }
    // else if(time_left < 0.20*total_time && time_left >= 0.10*total_time){
    //   move = this->ABMinMax(&game, 3);
    // }
    // else if(time_left < 0.30*total_time && time_left >= 0.20*total_time){
    //   move = this->ABMinMax(&game, 4);
    // }
    // else{
    //   for(int i = 1; i<=DEPTH; i++){
    //     //std::cerr << "Iter" << i << std::endl;
    //     move = this->ABMinMax(&game, i);
    //     int t_now = time(0);
    //     if(2*t_aim < (t_now - t_start)*(1+sz))
    //       break;
    //   }
    // }

    if(firstMove){
      std::cerr << "/* error message */" << std::endl;
      if(this->player == 0){
        move = "Fa1";
      }
      else{
        int x = oppMove[1];
        int y = oppMove[2] - '0';
        std::cerr << "/* error message */" << x << " " << y << std::endl;
        std::cerr << "Move: " << move << std::endl;
        if((x == 97 || x == (96+n)) && (y == 1 || y == n)){

          move = "F";
          move += (char)x + to_string(n+1-y);
          std::cerr << "Move Chosen: " << move << std::endl;
        }
        else{
          move = "F";
          if((x-97) > (96+n-x)){
            move += (char)(96+n);
          }
          else{
            move = move + 'a';
          }

          if((y-1) > (n-y)){
            move = move + to_string(n);
          }
          else{
            move = move + to_string(1);
          }
        }
      }
      firstMove = false;
    }
    else{
      switch (n) {
        case 5:
          if(time_left <= 30 && time_left > 2){
            move = this->ABMinMax(&game, 3);
          }
          else if(time_left <= 2){
            move = this->ABMinMax(&game, 2);
          }
          else{
              if(sz >= 95){
                move = this->ABMinMax(&game, 3);
              }
              else{
                move = this->ABMinMax(&game, 4);
              }
          }
          break;
        case 6:
          if(time_left <= 55 && time_left > 5){
            move = this->ABMinMax(&game, 3);
          }
          else if(time_left <= 5){
            move = this->ABMinMax(&game, 2);
          }
          else{

              if(sz >= 90){
                move = this->ABMinMax(&game, 3);
              }
              else{
                move = this->ABMinMax(&game, 4);
              }
          }
          break;
        case 7:
          if(time_left <= 20 && time_left > 2){
            move = this->ABMinMax(&game, 2);
          }
          else if(time_left <= 2){
            move = this->ABMinMax(&game, 1);
          }
          else{
            move = this->ABMinMax(&game, 3);
          }
          break;
      }
    }


    // std::cerr << "MINMAX" << univ_count << std::endl;

    //string move = all_moves[rand()%all_moves.size()];
    //std::cerr << "TakingMOVE " << all_moves[0] << std::endl;
    this->game.execute_move(move);
    // cerr<<"My Influence: "<<this->game.getInfluence(this->player)<<endl;
    move = move+'\n';
    //cerr<<"Chosen move: "<<move;
    cout<<move;
    cout<<flush;
    t_moveStart = time(0);
    time_left = time_left - (t_moveStart - t_start);
    cin>>move;
    this->game.execute_move(move);
  }
}


bool comp(pair<string, int> m1, pair<string, int> m2)
{
  return (m1.second>m2.second);
}

string MadanPlayer::ABMinMax(Board* current_game, int depth_limit){
  // std::cerr << "MINMAXSTARTED" << std::endl;
  //cerr<<"Current Depth: "<<depth_limit<<endl;
  return ABMaxMove(current_game, "", depth_limit, 1, -INT_MAX, INT_MAX);
}

string MadanPlayer::ABMaxMove(Board* current_game, string mv, int depth_limit, int depth, int a, int b){
  vector<string> moves;
  string best_move = "";
  string best_real_move = "";
  string move = "";
  int alpha = a, beta = b;

  if(depth >= depth_limit){
    moves = current_game->generate_all_moves(this->player);
    best_real_move = moves[0];
    //std::cerr << "RECURSIONENDING" << moves.size() << std::endl;
    int mvSize = moves.size();
    int eval_best_move = INT_MIN+100;
    for(int i=0; i<mvSize; i++){
      univ_count++;
      Board next = current_game->board_after_move(moves[i]);
      int eval_move = next.evaluate_board(this->player);

      if(next.isTerminalState(player)){
        current_game->miniMaxVal = INT_MAX-depth;
        // cerr<<"My winning state: "<<moves[i]<<endl;
        return moves[i];
      }
      else if(next.isTerminalState(1-player))
        continue;


      if(best_move == "" || eval_move > eval_best_move){
        best_move = moves[i];
        eval_best_move = eval_move;
        best_real_move = moves[i];
        alpha = eval_move;
      }
      if(alpha >= beta){
        current_game->miniMaxVal = eval_best_move;
        // cerr<<"Max: "<<best_real_move<<endl;
        return best_real_move;
      }
    }
    current_game->miniMaxVal = eval_best_move;
    //univ_count++;
    // cerr<<"Max: "<<best_real_move<<endl;
    return best_real_move;
  }
  else{
    moves = current_game->generate_all_moves(this->player);
    best_real_move = moves[0];
    //std::cerr << "ABMAX" << moves.size() << std::endl;

    int mvSize = moves.size();
    int eval_best_move = INT_MIN+100;
    // vector< pair<string,int> > sortedMoves(mvSize);
    // for(int i=0; i<mvSize; i++)
    // {
    //   sortedMoves[i] = make_pair(moves[i], (current_game->board_after_move(moves[i])).evaluate_board(this->player));
    // }
    // sort(sortedMoves.begin(), sortedMoves.end(), comp);
    for(int i=0; i<mvSize; i++){
      Board next_game = current_game->board_after_move(moves[i]);

      if(next_game.isTerminalState(player)){
        current_game->miniMaxVal = INT_MAX-depth;
        // cerr<<"My winning state: "<<moves[i]<<endl;
        return moves[i];
      }
      else if(next_game.isTerminalState(1-player))
        continue;

      move = ABMinMove(&next_game, mv, depth_limit, depth+1, alpha, beta);
      univ_count++;

      int eval_move = next_game.miniMaxVal;

      if(best_move == "" || eval_move > eval_best_move){ ////FORM of evaluate_board(string move, int player)
        best_move = moves[i];
        eval_best_move = eval_move;
        best_real_move = moves[i];
        alpha = eval_move;
      }
      if(alpha >= beta){
        current_game->miniMaxVal = eval_best_move;
        //univ_count++;
        // cerr<<"Max: "<<best_real_move<<endl;
        return best_real_move;
      }
    }
    current_game->miniMaxVal = eval_best_move;
    //univ_count++;
    // cerr<<"Max: "<<best_real_move<<endl;
    return best_real_move;
  }
}

string MadanPlayer::ABMinMove(Board* current_game, string mv, int depth_limit, int depth, int a, int b){
  vector<string> moves;
  string best_move = "";
  string best_real_move = "";
  string move = "";
  int alpha = a, beta = b;

  if(depth >= depth_limit){
    moves = current_game->generate_all_moves(1-this->player);
    best_real_move = moves[0];
    //std::cerr << "RECURSIONENDING" << moves.size() << std::endl;
    int mvSize = moves.size();
    int eval_best_move = INT_MAX;
    for(int i=0; i<mvSize; i++){
      Board next = current_game->board_after_move(moves[i]);
      int eval_move = next.evaluate_board(this->player);

      if(next.isTerminalState(1-player)){
        // cerr<<"!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!Terminal State!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n";
        current_game->miniMaxVal = INT_MIN+100+depth;
        // cerr<<"Opp winning state: "<<moves[i]<<endl;
        return moves[i];
      }

      univ_count++;

      if(best_move == "" || eval_move < eval_best_move){
        best_move = moves[i];
        eval_best_move = eval_move;
        best_real_move = moves[i];
        beta = eval_move;
      }
      if(alpha >= beta){
        //std::cerr << current_game->miniMaxVal << std::endl;
        current_game->miniMaxVal = eval_best_move;
        // cerr<<"Min: "<<best_real_move<<endl;
        return best_real_move;
      }
    }
    //std::cerr << current_game->miniMaxVal << std::endl;
    current_game->miniMaxVal = eval_best_move;
    // cerr<<"Min: "<<best_real_move<<endl;
    return best_real_move;
  }
  else{
    moves = current_game->generate_all_moves(1-this->player);
    best_real_move = moves[0];
    //std::cerr << "ADVERSARYSIZE" << move.size() << std::endl;
    int mvSize = moves.size();
    int eval_best_move = INT_MAX;

    // vector< pair<string,int> > sortedMoves(mvSize);
    // for(int i=0; i<mvSize; i++)
    // {
    //   sortedMoves[i] = make_pair(moves[i], (current_game->board_after_move(moves[i])).evaluate_board(this->player));
    // }
    // sort(sortedMoves.begin(), sortedMoves.end(), comp);

    for(int i=0; i<mvSize; i++){
      Board next_game = current_game->board_after_move(moves[i]);

      if(next_game.isTerminalState(1-player)){
        // cerr<<"!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!Terminal State!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n";
        // cerr << "Opp Terminal State: " << moves[i] << endl;
        current_game->miniMaxVal = INT_MIN+100+depth;
        return moves[i];
      }

      move = ABMaxMove(&next_game, mv, depth_limit, depth+1, alpha, beta);
      univ_count++;

      int eval_move = next_game.miniMaxVal;

      if(best_move == "" || eval_move < eval_best_move){ ////FORM of evaluate_board(string move, int player)
        best_move = moves[i];
        eval_best_move = eval_move;
        best_real_move = moves[i];
        beta = eval_move;
      }
      if(alpha >= beta){
        current_game->miniMaxVal = eval_best_move;
        // cerr<<"Min: "<<best_real_move<<endl;
        return best_real_move;
      }
    }
    current_game->miniMaxVal = eval_best_move;
    // cerr<<"Min: "<<best_real_move<<endl;
    return best_real_move;
  }
}

int main(){
  srand(time(0));

  MadanPlayer madan_player = MadanPlayer();
  return 0;
}

//FEEDOVER : Don't leave board in a dynamic state(CRITICAL STAGE)
//SECONDARY_SEARCH: Search down the selected move to ensure no drastic mishap
//Openings/Endgames: for some parts of the game (especially initial and end moves), keep a catalog of best moves to make.
