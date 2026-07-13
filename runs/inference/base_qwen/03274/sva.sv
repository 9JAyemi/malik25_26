module dffr_assertions (
    input logic CLK,
    input logic R,
    input logic D,
    output logic Q
);
    // Q can only transition from 0 to 1 when D is 1 and R is 0.
    dffr_1: assert property (
        @(posedge CLK) disable iff (!R) $rose(Q) |-> (D == 1'b1)
    );
    // Q can only transition from 1 to 0 when R is 0.
    dffr_2: assert property (
        @(posedge CLK) disable iff (!R) $fell(Q) |-> (R == 1'b0)
    );
    // Q is always 0 when R is 0.
    dffr_3: assert property (
        @(posedge CLK) disable iff (!R) Q == 1'b0
    );
    // Q is always equal to D when R is 1.
    dffr_4: assert property (
        @(posedge CLK) disable iff (R) Q == D
    );
endmodule