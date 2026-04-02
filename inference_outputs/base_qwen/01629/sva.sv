module binary_adder_sva(A, B, C);
    input logic [3:0] A, B;
    input logic [3:0] C;
    
    wire [3:0] s;
    wire [4:0] cout;
    
    fadd a0(A[0], B[0], 1'b0, s[0], cout[1]);
    fadd a1(A[1], B[1], cout[1], s[1], cout[2]);
    fadd a2(A[2], B[2], cout[2], s[2], cout[3]);
    fadd a3(A[3], B[3], cout[3], s[3], cout[4]);
    
    assign C = s;
    
    // Check that the sum is correct
    sum_correct: assert property (
        @(posedge clk) disable iff (!reset_n) (C == A + B)
    );
    
    // Check that the carry out is correct
    carry_out_correct: assert property (
        @(posedge clk) disable iff (!reset_n) (cout[4] == (A + B)[4])
    );
    
    // Check that the sum bits are correct
    sum_bits_correct: assert property (
        @(posedge clk) disable iff (!reset_n) (C == {cout[3:0], s})
    );
    
    // Check that the carry out bits are correct
    carry_out_bits_correct: assert property (
        @(posedge clk) disable iff (!reset_n) (cout == {cout[4], cout[3:1]})
    );
    
    // Check that the sum is within the valid range
    sum_within_range: assert property (
        @(posedge clk) disable iff (!reset_n) (C inside {[0:15]})
    );
    
    // Check that the carry out is either 0 or 1
    carry_out_within_range: assert property (
        @(posedge clk) disable iff (!reset_n) (cout[4] inside {[0:1]})
    );
    
    // Check that the sum bits are either 0 or 1
    sum_bits_within_range: assert property (
        @(posedge clk) disable iff (!reset_n) (C inside {[0:15]})
    );
    
    // Check that the carry out bits are either 0 or 1
    carry_out_bits_within_range: assert property (
        @(posedge clk) disable iff (!reset_n) (cout inside {[0:15]})
    );
    
    // Check that the sum is not all zeros when A and B are not all zeros
    sum_not_zero: assert property (
        @(posedge clk) disable iff (!reset_n) ((A != 4'b0000) && (B != 4'b0000) |-> (C != 4'b0000))
    );
    
    // Check that the carry out is not all zeros when A and B are not all zeros
    carry_out_not_zero: assert property (
        @(posedge clk) disable iff (!reset_n) ((A != 4'b0000) && (B != 4'b0000) |-> (cout[4] != 1'b0))
    );
endmodule