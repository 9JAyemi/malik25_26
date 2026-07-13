module alu_sva (
    input logic clk,                // sampling clock for SVA (DUT is combinational)
    input logic [3:0]  ctl,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [31:0] out,
    input logic        zero
);
    // zero output must reflect whether out equals zero
    check_zero_definition: assert property (
        @(posedge clk) disable iff (1'b0) zero == (out == 32'd0)
    );

    // ctl==0: out is bitwise AND
    check_ctl0_and: assert property (
        @(posedge clk) disable iff (1'b0) (ctl == 4'd0) |-> (out == (a & b))
    );

    // ctl==1: out is bitwise OR
    check_ctl1_or: assert property (
        @(posedge clk) disable iff (1'b0) (ctl == 4'd1) |-> (out == (a | b))
    );

    // ctl==2: out is addition
    check_ctl2_add: assert property (
        @(posedge clk) disable iff (1'b0) (ctl == 4'd2) |-> (out == (a + b))
    );

    // ctl==6: out is subtraction
    check_ctl6_sub: assert property (
        @(posedge clk) disable iff (1'b0) (ctl == 4'd6) |-> (out == (a - b))
    );

    // ctl==7: out is {31'b0, slt} using RTL's slt/oflow_sub definition
    check_ctl7_slt: assert property (
        @(posedge clk) disable iff (1'b0)
            (ctl == 4'd7) |-> (out == {31'b0, (((a[31] == b[31]) && (((a - b)[31]) != a[31])) ? ~a[31] : a[31])})
    );

    // ctl==12: out is bitwise NOR
    check_ctl12_nor: assert property (
        @(posedge clk) disable iff (1'b0) (ctl == 4'd12) |-> (out == ~(a | b))
    );

    // ctl==13: out is bitwise XOR
    check_ctl13_xor: assert property (
        @(posedge clk) disable iff (1'b0) (ctl == 4'd13) |-> (out == (a ^ b))
    );

    // default case: out is zero for unsupported ctl values
    check_default_zero: assert property (
        @(posedge clk) disable iff (1'b0)
            (!(ctl inside {4'd0,4'd1,4'd2,4'd6,4'd7,4'd12,4'd13})) |-> (out == 32'd0)
    );
endmodule