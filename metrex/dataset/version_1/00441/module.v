
module FourBitFA(FA,FB,FCin,FSum,FCout);

parameter SIZE=4;

input [SIZE-1:0]FA,FB;
output [SIZE-1:0]FSum;
input FCin;
output FCout;

wire [SIZE-1:0] FTemp;

FA FA1(.A(FA[0]),.B(FB[0]),.Cin(FCin),.Sum(FSum[0]),.Cout(FTemp[0])),
FA2(.A(FA[1]),.B(FB[1]),.Cin(FTemp[0]),.Sum(FSum[1]),.Cout(FTemp[1])),
FA3(.A(FA[2]),.B(FB[2]),.Cin(FTemp[1]),.Sum(FSum[2]),.Cout(FTemp[2])),
FA4(.A(FA[3]),.B(FB[3]),.Cin(FTemp[2]),.Sum(FSum[3]),.Cout(FCout));

endmodule

module FA(A,B,Cin,Sum,Cout);

input A,B,Cin;
output Sum,Cout;

assign Sum = (A^B)^Cin;
assign Cout = (A&B)|(A&Cin)|(B&Cin);
                                                                         
endmodule
