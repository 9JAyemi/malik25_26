```systemverilog
module twos_complement_sva (
    input logic [3:0] binary,
    output logic [3:0] twos_comp
);
    // Combinational logic: invert and add_one are calculated at each clock edge
    // twos_comp is updated at each clock edge
    // No clock or reset signals are present in the RTL

    // Property to check that invert is correctly calculated as the bitwise NOT of binary
    invert_calculation: assert property (
        @(posedge CLK) disable iff (!RESETn) (invert == ~binary)
    );

    // Property to check that add_one is correctly calculated as invert + 1
    add_one_calculation: assert property (
        @(posedge CLK) disable iff (!RESETn) (add_one == invert + 4'b0001)
    );

    // Property to check that twos_comp is correctly calculated as add_one
    twos_comp_calculation: assert property (
        @(posedge CLK) disable iff (!RESETn) (twos_comp == add_one)
    );
endmodule
```