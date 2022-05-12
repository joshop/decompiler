int main(){
  int n = 0;
  int* p = &n;
  *p = 1;
  if(*p == n){return 1;}
  return 0;
}
