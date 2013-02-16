#include <stddef.h>


struct message {
  int bufsize;
  int (*serialize)(void *p, unsigned char *buf);
  void (*deserialize)(void *p, unsigned char *buf, int length);
};

struct intpair {int x, y;};

int intpair_serialize(struct intpair *p, unsigned char *buf) {
  int x = p->x;
  int y = p->y;
  ((int *)buf)[0]=x;
  ((int *)buf)[1]=y;
  return 8;
}
  
void intpair_deserialize(struct intpair *p, unsigned char *buf, int length) {
  int x = ((int *)buf)[0];
  int y = ((int *)buf)[1];
  p->x = x;
  p->y = y;
}
  
struct message intpair_message = 
  {8, &intpair_serialize, &intpair_deserialize};

int main(void) {
  struct intpair p,q;
  unsigned char buf[8];
  int len, x,y;

  p.x = 1;
  p.y = 2;
  len = intpair_message.serialize(&p, buf);
  intpair_message.deserialize(&q, buf, 8);
  x = q.x;
  y = q.y;
  return x+y;
}
  
  
    
   



