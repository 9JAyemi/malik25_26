module coordinate_cordic
(
	realIn,
	imagIn,
	clk,
	amplitude,
	angle,
	test1,
	test2
);

input signed [INWIDTH-1:0]realIn,imagIn;
input clk;
output signed [OUTWIDTH-1:0]amplitude;
output signed [ANGLEWIDTH-1:0]angle;

input  [9:0] test1;
output  [9:0] test2;
assign  test2 = {11{test1}};
parameter INWIDTH = 18,  OUTWIDTH = 20, MIDWIDTH = 21, ANGLEWIDTH =15;parameter ARCTANG_0  = 12'b10_01110_00100,ARCTANG_1  = 11'b1_01110_00100,ARCTANG_2  = 10'b11000_01100,ARCTANG_3  = 9'b1100_01100,ARCTANG_4  = 8'b110_00111,ARCTANG_5  = 7'b11_00011,ARCTANG_6  = 6'b1_10010,ARCTANG_7  = 5'b11001,ARCTANG_8  = 4'b1100,ARCTANG_9  = 3'b110,ARCTANG_10 = 2'b11,ARCTANG_11 = 2'b10;parameter HALFPI = 13'b100_11100_01000;reg signed [MIDWIDTH-1:0]xData1,xData2,xData3,xData4,xData5,xData6,
                         xData7,xData8,xData9,xData10,xData11,xData12,
                         xData13,xData14,xData15,xData16,
				         yData1,yData2,yData3,yData4,yData5,yData6,
				         yData7,yData8,yData9,yData10,yData11,yData12,
				         yData13,yData14,yData15,yData16;

reg signed [ANGLEWIDTH-1:0]angle1,angle2,angle3,angle4,angle5,angle6,
					       angle7,angle8,angle9,angle10,angle11,angle12,
					       angle13,angle14,angle15,angle16;


wire signed [MIDWIDTH-1:0]reIn,imIn;
wire signed [ANGLEWIDTH-1:0]ang;
assign reIn = realIn[INWIDTH-1]?(imagIn[INWIDTH-1]?-imagIn:imagIn):realIn;
assign imIn = realIn[INWIDTH-1]?(imagIn[INWIDTH-1]?realIn:-realIn):imagIn;
assign ang = realIn[INWIDTH-1]?(imagIn[INWIDTH-1]?-HALFPI:HALFPI):1'b0;


assign amplitude = {xData12[MIDWIDTH-1],xData12[MIDWIDTH-3:0]};
assign angle = angle12;



always@(posedge clk)
begin
    xData1 <= imIn[MIDWIDTH-1]?(reIn - imIn):(reIn + imIn);
	yData1 <= imIn[MIDWIDTH-1]?(imIn + reIn):(imIn - reIn);
	angle1 <= imIn[MIDWIDTH-1]?(ang - ARCTANG_0):(ang + ARCTANG_0);

    xData2 <= yData1[MIDWIDTH-1]?(xData1 - {{2{yData1[MIDWIDTH-1]}},yData1[MIDWIDTH-2:1]}):(xData1 + {{2{yData1[MIDWIDTH-1]}},yData1[MIDWIDTH-2:1]});
	yData2 <= yData1[MIDWIDTH-1]?(yData1 + {{2{xData1[MIDWIDTH-1]}},xData1[MIDWIDTH-2:1]}):(yData1 - {{2{xData1[MIDWIDTH-1]}},xData1[MIDWIDTH-2:1]});
	angle2 <= yData1[MIDWIDTH-1]?(angle1 - ARCTANG_1):(angle1 + ARCTANG_1);

    xData3 <= yData2[MIDWIDTH-1]?(xData2 - {{3{yData2[MIDWIDTH-1]}},yData2[MIDWIDTH-2:2]}):(xData2 + {{3{yData2[MIDWIDTH-1]}},yData2[MIDWIDTH-2:2]});
	yData3 <= yData2[MIDWIDTH-1]?(yData2 + {{3{xData2[MIDWIDTH-1]}},xData2[MIDWIDTH-2:2]}):(yData2 - {{3{xData2[MIDWIDTH-1]}},xData2[MIDWIDTH-2:2]});
	angle3 <= yData2[MIDWIDTH-1]?(angle2 - ARCTANG_2):(angle2 + ARCTANG_2);

    xData4 <= yData3[MIDWIDTH-1]?(xData3 - {{4{yData3[MIDWIDTH-1]}},yData3[MIDWIDTH-2:3]}):(xData3 + {{4{yData3[MIDWIDTH-1]}},yData3[MIDWIDTH-2:3]});
	yData4 <= yData3[MIDWIDTH-1]?(yData3 + {{4{xData3[MIDWIDTH-1]}},xData3[MIDWIDTH-2:3]}):(yData3 - {{4{xData3[MIDWIDTH-1]}},xData3[MIDWIDTH-2:3]});
	angle4 <= yData3[MIDWIDTH-1]?(angle3 - ARCTANG_3):(angle3 + ARCTANG_3);

    xData5 <= yData4[MIDWIDTH-1]?(xData4 - {{5{yData4[MIDWIDTH-1]}},yData4[MIDWIDTH-2:4]}):(xData4 + {{5{yData4[MIDWIDTH-1]}},yData4[MIDWIDTH-2:4]});
	yData5 <= yData4[MIDWIDTH-1]?(yData4 + {{5{xData4[MIDWIDTH-1]}},xData4[MIDWIDTH-2:4]}):(yData4 - {{5{xData4[MIDWIDTH-1]}},xData4[MIDWIDTH-2:4]});
	angle5 <= yData4[MIDWIDTH-1]?(angle4 - ARCTANG_4):(angle4 + ARCTANG_4);

    xData6 <= yData5[MIDWIDTH-1]?(xData5 - {{6{yData5[MIDWIDTH-1]}},yData5[MIDWIDTH-2:5]}):(xData5 + {{6{yData5[MIDWIDTH-1]}},yData5[MIDWIDTH-2:5]});
	yData6 <= yData5[MIDWIDTH-1]?(yData5 + {{6{xData5[MIDWIDTH-1]}},xData5[MIDWIDTH-2:5]}):(yData5 - {{6{xData5[MIDWIDTH-1]}},xData5[MIDWIDTH-2:5]});
	angle6 <= yData5[MIDWIDTH-1]?(angle5 - ARCTANG_5):(angle5 + ARCTANG_5);

    xData7 <= yData6[MIDWIDTH-1]?(xData6 - {{7{yData6[MIDWIDTH-1]}},yData6[MIDWIDTH-2:6]}):(xData6 + {{7{yData6[MIDWIDTH-1]}},yData6[MIDWIDTH-2:6]});
	yData7 <= yData6[MIDWIDTH-1]?(yData6 + {{7{xData6[MIDWIDTH-1]}},xData6[MIDWIDTH-2:6]}):(yData6 - {{7{xData6[MIDWIDTH-1]}},xData6[MIDWIDTH-2:6]});
	angle7 <= yData6[MIDWIDTH-1]?(angle6 - ARCTANG_6):(angle6 + ARCTANG_6);

    xData8 <= yData7[MIDWIDTH-1]?(xData7 - {{8{yData7[MIDWIDTH-1]}},yData7[MIDWIDTH-2:7]}):(xData7 + {{8{yData7[MIDWIDTH-1]}},yData7[MIDWIDTH-2:7]});
	yData8 <= yData7[MIDWIDTH-1]?(yData7 + {{8{xData7[MIDWIDTH-1]}},xData7[MIDWIDTH-2:7]}):(yData7 - {{8{xData7[MIDWIDTH-1]}},xData7[MIDWIDTH-2:7]});
	angle8 <= yData7[MIDWIDTH-1]?(angle7 - ARCTANG_7):(angle7 + ARCTANG_7);

    xData9 <= yData8[MIDWIDTH-1]?(xData8 - {{9{yData8[MIDWIDTH-1]}},yData8[MIDWIDTH-2:8]}):(xData8 + {{9{yData8[MIDWIDTH-1]}},yData8[MIDWIDTH-2:8]});
	yData9 <= yData8[MIDWIDTH-1]?(yData8 + {{9{xData8[MIDWIDTH-1]}},xData8[MIDWIDTH-2:8]}):(yData8 - {{9{xData8[MIDWIDTH-1]}},xData8[MIDWIDTH-2:8]});
	angle9 <= yData8[MIDWIDTH-1]?(angle8 - ARCTANG_8):(angle8 + ARCTANG_8);

    xData10 <= yData9[MIDWIDTH-1]?(xData9 - {{10{yData9[MIDWIDTH-1]}},yData9[MIDWIDTH-2:9]}):(xData9 + {{10{yData9[MIDWIDTH-1]}},yData9[MIDWIDTH-2:9]});
	yData10 <= yData9[MIDWIDTH-1]?(yData9 + {{10{xData9[MIDWIDTH-1]}},xData9[MIDWIDTH-2:9]}):(yData9 - {{10{xData9[MIDWIDTH-1]}},xData9[MIDWIDTH-2:9]});
	angle10 <= yData9[MIDWIDTH-1]?(angle9 - ARCTANG_9):(angle9 + ARCTANG_9);

    xData11 <= yData10[MIDWIDTH-1]?(xData10 - {{11{yData10[MIDWIDTH-1]}},yData10[MIDWIDTH-2:10]}):(xData10 + {{11{yData10[MIDWIDTH-1]}},yData10[MIDWIDTH-2:10]});
	yData11 <= yData10[MIDWIDTH-1]?(yData10 + {{11{xData10[MIDWIDTH-1]}},xData10[MIDWIDTH-2:10]}):(yData10 - {{11{xData10[MIDWIDTH-1]}},xData10[MIDWIDTH-2:10]});
	angle11 <= yData10[MIDWIDTH-1]?(angle10 - ARCTANG_10):(angle10 + ARCTANG_10);

    xData12 <= yData11[MIDWIDTH-1]?(xData11 - {{12{yData11[MIDWIDTH-1]}},yData11[MIDWIDTH-2:11]}):(xData11 + {{12{yData11[MIDWIDTH-1]}},yData11[MIDWIDTH-2:11]});
	yData12 <= yData11[MIDWIDTH-1]?(yData11 + {{12{xData11[MIDWIDTH-1]}},xData11[MIDWIDTH-2:11]}):(yData11 - {{12{xData11[MIDWIDTH-1]}},xData11[MIDWIDTH-2:11]});
	angle12 <= yData11[MIDWIDTH-1]?(angle11 - ARCTANG_11):(angle11 + ARCTANG_11);
	
   
	
end	
endmodule
