module init_sva (
    input logic clk,
    input logic ini
);

    // ini starts low before the first clocked update.
    check_ini_initial_low: assert property (
        @(posedge clk) $initstate |-> (ini == 1'b0)
    );

    // If ini is low at a clock edge, it is high on the next clock edge.
    check_ini_low_becomes_high: assert property (
        @(posedge clk) (ini == 1'b0) |=> (ini == 1'b1)
    );

    // Once ini is high, it remains high on later clock edges.
    check_ini_stays_high: assert property (
        @(posedge clk) (ini == 1'b1) |=> (ini == 1'b1)
    );

endmodule