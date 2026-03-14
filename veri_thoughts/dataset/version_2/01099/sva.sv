module priority_encoder_and_ripple_carry_adder_sva (
    input logic clk,
    input logic [3:0] I,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic select,
    input logic [1:0] Y,
    input logic [3:0] Sum
);

    // When select=0, Sum is forced to zero.
    check_select0_sum_zero: assert property (
        @(posedge clk) (select == 1'b0) |-> (Sum == 4'b0000)
    );

    // When select=1, Y is forced to zero.
    check_select1_y_zero: assert property (
        @(posedge clk) (select == 1'b1) |-> (Y == 2'b00)
    );

    // When select=1, Sum equals A+B+Cin (low 4 bits).
    check_select1_sum_matches_adder: assert property (
        @(posedge clk) (select == 1'b1) |-> (Sum == (A + B + Cin))
    );

    // For select=0 and I==0001, Y==00.
    check_pe_sel0_i0001: assert property (
        @(posedge clk) (select == 1'b0 && I == 4'b0001) |-> (Y == 2'b00)
    );

    // For select=0 and I==0010, Y==01.
    check_pe_sel0_i0010: assert property (
        @(posedge clk) (select == 1'b0 && I == 4'b0010) |-> (Y == 2'b01)
    );

    // For select=0 and I==0100, Y==10.
    check_pe_sel0_i0100: assert property (
        @(posedge clk) (select == 1'b0 && I == 4'b0100) |-> (Y == 2'b10)
    );

    // For select=0 and I==1000, Y==11.
    check_pe_sel0_i1000: assert property (
        @(posedge clk) (select == 1'b0 && I == 4'b1000) |-> (Y == 2'b11)
    );

    // For select=0 and non-onehot I, Y==00 (default case).
    check_pe_sel0_default: assert property (
        @(posedge clk) (select == 1'b0 && !$onehot(I)) |-> (Y == 2'b00)
    );

    // Y==01 occurs only when select=0 and I==0010.
    check_y01_implies_i0010_sel0: assert property (
        @(posedge clk) (Y == 2'b01) |-> (select == 1'b0 && I == 4'b0010)
    );

    // Y==10 occurs only when select=0 and I==0100.
    check_y10_implies_i0100_sel0: assert property (
        @(posedge clk) (Y == 2'b10) |-> (select == 1'b0 && I == 4'b0100)
    );

    // Y==11 occurs only when select=0 and I==1000.
    check_y11_implies_i1000_sel0: assert property (
        @(posedge clk) (Y == 2'b11) |-> (select == 1'b0 && I == 4'b1000)
    );

    // Y and Sum are never both non-zero simultaneously.
    check_outputs_not_both_nonzero: assert property (
        @(posedge clk) !((|Y) && (|Sum))
    );

endmodule