```systemverilog
module MUXCY_assertions (
    input logic CLK,
    input logic RESETn,
    input logic CI,
    input logic DI,
    input logic S,
    input logic CIN,
    output logic O,
    output logic CO
);
    // Sequential logic is not present, so all assertions will be clocked.

    // CI can only transition from HIGH to LOW when DI is LOW and S is LOW.
    sequential_1: assert property (
        @(posedge CLK) disable iff (!RESETn) $fell(CI) |-> (DI == 1'b0) && (S == 1'b0)
    );

    // DI can only transition from HIGH to LOW when CI is LOW and S is LOW.
    sequential_2: assert property (
        @(posedge CLK) disable iff (!RESETn) $fell(DI) |-> (CI == 1'b0) && (S == 1'b0)
    );

    // S can only transition from HIGH to LOW when CI is LOW and DI is LOW.
    sequential_3: assert property (
        @(posedge CLK) disable iff (!RESETn) $fell(S) |-> (CI == 1'b0) && (DI == 1'b0)
    );

    // CIN can only transition from HIGH to LOW when CI is LOW and DI is LOW.
    sequential_4: assert property (
        @(posedge CLK) disable iff (!RESETn) $fell(CIN) |-> (CI == 1'b0) && (DI == 1'b0)
    );

    // O is the result of the OR operation between A and B.
    sequential_5: assert property (
        @(posedge CLK) disable iff (!RESETn) O |-> (O == (CI & S) | (DI & (CI | S)))
    );

    // CO is the result of the OR operation between C and D.
    sequential_6: assert property (
        @(posedge CLK) disable iff (!RESETn) CO |-> (CO == (CI & S) | (DI & (CI | S)))
    );

    // At reset assertion, O and CO must drive LOW.
    reset: assert property (
        @(posedge CLK) !RESETn |-> (O == 1'b0) && (CO == 1'b0)
    );
endmodule
```