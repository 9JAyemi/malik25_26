```systemverilog
module top_module_sva (
    input logic CLK,
    input logic RESETn,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic sel,
    output logic [3:0] OUT
);

    wire [3:0] wire_twos_comp;

    twos_complement twos_comp(
        .A(A),
        .OUT(wire_twos_comp)
    );

    mux_2to1 mux(
        .A(wire_twos_comp),
        .B(B),
        .sel(sel),
        .OUT(OUT)
    );

    // Twos complement logic should produce the correct twos complement of A
    twos_comp_check: assert property (
        @(posedge CLK) disable iff (!RESETn) (wire_twos_comp == ~A + 1)
    );

    // Mux should select between A and B based on sel
    mux_select_check: assert property (
        @(posedge CLK) disable iff (!RESETn) (OUT == (sel ? A : B))
    );

    // At reset, the output of the twos complement should be 0
    reset_twos_comp_check: assert property (
        @(posedge CLK) !RESETn |-> (wire_twos_comp == 4'b0)
    );

    // At reset, the output of the mux should be 0
    reset_mux_check: assert property (
        @(posedge CLK) !RESETn |-> (OUT == 4'b0)
    );

endmodule
```