```systemverilog
module shift_register_sva (
    input logic clk,
    input logic areset,
    input logic load,
    input logic ena,
    input logic [3:0] data,
    output logic [3:0] q
);
    // Reset behavior: q should be 0000 at reset
    reset: assert property (
        @(posedge clk) disable iff (!areset) (q == 4'b0000)
    );

    // Load behavior: q should be equal to data when load is asserted
    load_behavior: assert property (
        @(posedge clk) disable iff (!areset) (load |-> (q == data))
    );

    // Enable behavior: q should shift right when ena is asserted
    enable_behavior: assert property (
        @(posedge clk) disable iff (!areset) (ena |-> (q == {q[2:0], q[3]}))
    );

    // Combinational logic behavior: q should not change when neither load nor ena is asserted
    combinational_behavior: assert property (
        @(posedge clk) disable iff (!areset) (!load && !ena |-> (q == q))
    );

endmodule
```