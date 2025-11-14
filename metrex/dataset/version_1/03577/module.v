module shifter(
input [31:0] A, input [31:0] B, input aluc1,input aluc0,output  [31:0] Result,output Zero,
output Carry,
output Negative,
output Overflow
);
reg [31:0] Result_temp;
reg Zero_temp;
reg Carry_temp;
reg Nagative_temp;
reg Overflow_temp;
reg [4:0] shift_amount;


assign Zero     = Zero_temp;
assign Carry    = Carry_temp;
assign Negative = Nagative_temp;
assign Overflow = Overflow_temp;
assign Result   = Result_temp;

always @(*) begin
    if( aluc1 == 0 && aluc0 == 0 )begin shift_amount = A[4:0];
        Result_temp = $signed(B)>>>shift_amount;
        if( Result_temp == 0 ) 
            Zero_temp = 1;
        else 
            Zero_temp = 0;
        Nagative_temp = B[31];
        if ( shift_amount == 0) 
            Carry_temp = 0;
        else 
            Carry_temp = B[shift_amount -1];
        Overflow_temp = 0;
        Nagative_temp=Result_temp[31];
    end
    else if( aluc1 == 0 && aluc0 == 1 )begin shift_amount = A[4:0];
        Result_temp = B >> shift_amount;
        if(Result_temp==0) 
            Zero_temp=1;
        else 
            Zero_temp=0;
        if(shift_amount==0)
            Carry_temp=0;
        else
        Carry_temp=B[shift_amount-1];
        Overflow_temp=0;
        Nagative_temp = Result_temp[31];
    end
    else if( aluc1 == 1 && aluc0 == 0 )begin  shift_amount = A[4:0];
        Result_temp = B<<shift_amount;
        if ( Result_temp == 0)
            Zero_temp = 1;
        else 
            Zero_temp = 0;
        if ( shift_amount ==0)
            Carry_temp = 0;
        else 
            Carry_temp=B[32-shift_amount]; 
        Overflow_temp = 0;  
        Nagative_temp = Result_temp[31];
    end
    else if( aluc1 == 1 && aluc0 == 1 )begin shift_amount = A[4:0];
        Result_temp=B<<shift_amount;
        if (Result_temp == 0)
            Zero_temp = 1;
        else Zero_temp = 0;
        if (shift_amount ==0)
          Carry_temp = 0;
        else 
        Carry_temp=B[32-shift_amount];
        Overflow_temp = 0;
        Nagative_temp = Result_temp[31];
    end
end
endmodule   