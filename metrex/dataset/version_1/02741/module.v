
module MUX41X1 (IN1,IN2,IN3,IN4,S0,S1,Q);

 input IN1,IN2,IN3,IN4,S0,S1;
 output Q;

 wire t1,t2;

 assign t1 = (S1 & IN1) | (~S1 & IN2);
 assign t2 = (S1 & IN3) | (~S1 & IN4);
 assign Q = (S0 & t1) | (~S0 & t2);

endmodule
