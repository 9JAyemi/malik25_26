module alu_sva (
    input  logic        CLK,
    input  logic        RESETn,   // External assertion clock/reset (DUT is combinational; no reset in RTL)
    input  logic [3:0]  ctl,
    input  logic [31:0] a,
    input  logic [31:0] b,
    input  logic [31:0] out,
    input  logic        zero,
    input  logic        oflow
);
    // Helper: signed-add overflow per RTL
    function automatic logic ovf_add (input logic [31:0] aa, input logic [31:0] bb);
        ovf_add = (aa[31] == bb[31]) && (((aa + bb)[31]) != aa[31]);
    endfunction
    // Helper: signed-sub overflow per RTL
    function automatic logic ovf_sub (input logic [31:0] aa, input logic [31:0] bb);
        ovf_sub = (aa[31] == bb[31]) && (((aa - bb)[31]) != aa[31]);
    endfunction
    // Helper: SLT bit per RTL
    function automatic logic slt_bit (input logic [31:0] aa, input logic [31:0] bb);
        slt_bit = ovf_sub(aa, bb) ? ~aa[31] : aa[31];
    endfunction

    ///// Output flag relations /////
    // zero is 1 iff out == 0.
    check_zero_definition: assert property (
        @(posedge CLK) disable iff (!RESETn)
        zero == (out == 32'h0000_0000)
    );

    // oflow equals add-overflow when ctl==2.
    check_oflow_add_sel: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (ctl == 4'd2) |-> (oflow == ovf_add(a, b))
    );

    // oflow equals sub-overflow when ctl!=2.
    check_oflow_else_sub: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (ctl != 4'd2) |-> (oflow == ovf_sub(a, b))
    );

    ///// ALU operation results /////
    // AND: ctl==0 => out == a & b.
    check_out_and: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (ctl == 4'd0) |-> (out == (a & b))
    );

    // OR: ctl==1 => out == a | b.
    check_out_or: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (ctl == 4'd1) |-> (out == (a | b))
    );

    // ADD: ctl==2 => out == a + b.
    check_out_add: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (ctl == 4'd2) |-> (out == (a + b))
    );

    // SUB: ctl==6 => out == a - b.
    check_out_sub: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (ctl == 4'd6) |-> (out == (a - b))
    );

    // SLT: ctl==7 => out == {31'b0, slt_bit}.
    check_out_slt: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (ctl == 4'd7) |-> (out == {31'h0, slt_bit(a, b)})
    );

    // NOR: ctl==12 => out == ~(a | b).
    check_out_nor: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (ctl == 4'd12) |-> (out == ~(a | b))
    );

    // XOR: ctl==13 => out == a ^ b.
    check_out_xor: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (ctl == 4'd13) |-> (out == (a ^ b))
    );

    // Default case: for unsupported ctl, out == 0.
    check_out_default_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ((ctl != 4'd2) && (ctl != 4'd0) && (ctl != 4'd12) &&
         (ctl != 4'd1) && (ctl != 4'd7) && (ctl != 4'd6) &&
         (ctl != 4'd13)) |-> (out == 32'h0000_0000)
    );

endmodule