module dffre_sva (
    input logic CLK,
    input logic RST,
    input logic EN,
    input logic SE,
    input logic [SIZE-1:0] DIN,
    input logic [SIZE-1:0] SI,
    output logic [SIZE-1:0] SO
);
    parameter SIZE = 1;

    ///// Sequential logic rules /////
    // Q can only transition from 0 to 1 when SE is 1 and SI is 1.
    scan_enable_1: assert property (
        @(posedge CLK) disable iff (!RST) $rose(Q) |-> (SE == 1'b1) && (SI == 1'b1)
    );
    // Q can only transition from 0 to 1 when RST is 1.
    reset_1: assert property (
        @(posedge CLK) disable iff (!RST) $rose(Q) |-> RST == 1'b1
    );
    // Q can only transition from 0 to 1 when EN is 1 and DIN is 1.
    enable_1: assert property (
        @(posedge CLK) disable iff (!RST) $rose(Q) |-> (EN == 1'b1) && (DIN == 1'b1)
    );
    // Q can only transition from 1 to 0 when SE is 0 and RST is 0 and EN is 0.
    scan_enable_0: assert property (
        @(posedge CLK) disable iff (!RST) $fell(Q) |-> (SE == 1'b0) && (RST == 1'b0) && (EN == 1'b0)
    );
    // Q can only transition from 1 to 0 when RST is 0 and EN is 0.
    reset_0: assert property (
        @(posedge CLK) disable iff (!RST) $fell(Q) |-> (RST == 1'b0) && (EN == 1'b0)
    );
    // Q can only transition from 1 to 0 when EN is 0.
    enable_0: assert property (
        @(posedge CLK) disable iff (!RST) $fell(Q) |-> (EN == 1'b0)
    );

    ///// Output rules /////
    // SO should always be equal to Q.
    output_1: assert property (
        @(posedge CLK) disable iff (!RST) SO == Q
    );
endmodule