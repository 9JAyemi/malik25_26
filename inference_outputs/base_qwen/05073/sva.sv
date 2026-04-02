module alu_sva (
    input logic CLK,
    input logic RESETn,
    input logic I0,
    input logic I1,
    input logic I3,
    input logic CIN,
    input logic [3:0] ALU_MODE,
    output logic SUM,
    output logic COUT
);
    // ALU_MODE should not transition from 0 to 15 during operation
    mode_transition: assert property (
        @(posedge CLK) disable iff (!RESETn) $rose(ALU_MODE) |-> (ALU_MODE inside {[0:15]})
    );

    // SUM should be 0 when ALU_MODE is 0 (unsupported mode)
    unsupported_mode_sum: assert property (
        @(posedge CLK) disable iff (!RESETn) (ALU_MODE == 4'b0000) |-> (SUM == 1'b0)
    );

    // COUT should be 0 when ALU_MODE is 0 (unsupported mode)
    unsupported_mode_cout: assert property (
        @(posedge CLK) disable iff (!RESETn) (ALU_MODE == 4'b0000) |-> (COUT == 1'b0)
    );

    // SUM should be I0 when ALU_MODE is 10 (CUP)
    cup_sum: assert property (
        @(posedge CLK) disable iff (!RESETn) (ALU_MODE == 4'b1010) |-> (SUM == I0)
    );

    // COUT should be 0 when ALU_MODE is 10 (CUP)
    cup_cout: assert property (
        @(posedge CLK) disable iff (!RESETn) (ALU_MODE == 4'b1010) |-> (COUT == 1'b0)
    );

    // SUM should be ~I0 when ALU_MODE is 11 (CDN)
   cdn_sum: assert property (
        @(posedge CLK) disable iff (!RESETn) (ALU_MODE == 4'b1011) |-> (SUM == ~I0)
    );

    // COUT should be 1 when ALU_MODE is 11 (CDN)
   cdn_cout: assert property (
        @(posedge CLK) disable iff (!RESETn) (ALU_MODE == 4'b1011) |-> (COUT == 1'b1)
    );

    // SUM should be I0 when ALU_MODE is 12 (CUPCDN) and I3 is 1
    cupcdn_sum_add: assert property (
        @(posedge CLK) disable iff (!RESETn) (ALU_MODE == 4'b1100) && (I3 == 1'b1) |-> (SUM == I0)
    );

    // COUT should be 0 when ALU_MODE is 12 (CUPCDN) and I3 is 1
    cupcdn_cout_add: assert property (
        @(posedge CLK) disable iff (!RESETn) (ALU_MODE == 4'b1100) && (I3 == 1'b1) |-> (COUT == 1'b0)
    );

    // SUM should be ~I0 when ALU_MODE is 12 (CUPCDN) and I3 is 0
    cupcdn_sum_sub: assert property (
        @(posedge CLK) disable iff (!RESETn) (ALU_MODE == 4'b1100) && (I3 == 1'b0) |-> (SUM == ~I0)
    );

    // COUT should be 1 when ALU_MODE is 12 (CUPCDN) and I3 is 0
    cupcdn_cout_sub: assert property (
        @(posedge CLK) disable iff (!RESETn) (ALU_MODE == 4'b1100) && (I3 == 1'b0) |-> (COUT == 1'b1)
    );

    // SUM should be I0 & I1 when ALU_MODE is 13 (MULT)
    mult_sum: assert property (
        @(posedge CLK) disable iff (!RESETn) (ALU_MODE == 4'b1101) |-> (SUM == (I0 & I1))
    );

    // COUT should be I0 & I1 when ALU_MODE is 13 (MULT)
    mult_cout: assert property (
        @(posedge CLK) disable iff (!RESETn) (ALU_MODE == 4'b1101) |-> (COUT == (I0 & I1))
    );
endmodule