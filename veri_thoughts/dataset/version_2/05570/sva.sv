module top_module_assertions (
    input logic clk,
    input logic reset,
    input logic [2:0] sel,
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] data3,
    input logic [3:0] data4,
    input logic [3:0] data5,
    input logic [7:0] d,
    input logic select,
    input logic [7:0] q
);

    // Reset forces q to zero.
    check_reset_clears_q: assert property (
        @(posedge clk) (reset == 1'b0) |-> (q == 8'b00000000)
    );

    // q remains zero on the first clock after reset was low.
    check_q_zero_first_cycle_after_reset: assert property (
        @(posedge clk) disable iff (!reset)
        ($past(reset, 1) == 1'b0) |-> (q == 8'b00000000)
    );

    // Without a select pulse two cycles earlier, q holds its previous value.
    check_q_holds_when_select_low: assert property (
        @(posedge clk) disable iff (!reset)
        (($past(reset, 1) == 1'b1) &&
         ($past(reset, 2) == 1'b1) &&
         ($past(select, 2) == 1'b0))
        |-> (q == $past(q, 1))
    );

    // A select pulse copies the previous low nibble into q[7:4].
    check_q_high_nibble_shifts_previous_low_nibble: assert property (
        @(posedge clk) disable iff (!reset)
        (($past(reset, 1) == 1'b1) &&
         ($past(reset, 2) == 1'b1) &&
         ($past(select, 2) == 1'b1))
        |-> (q[7:4] == $past(q[3:0], 1))
    );

    // sel=000 loads data0 into q[3:0] two clocks later.
    check_q_low_nibble_loads_data0: assert property (
        @(posedge clk) disable iff (!reset)
        (($past(reset, 1) == 1'b1) &&
         ($past(reset, 2) == 1'b1) &&
         ($past(select, 2) == 1'b1) &&
         ($past(sel, 2) == 3'b000))
        |-> (q[3:0] == $past(data0, 2))
    );

    // sel=001 loads data1 into q[3:0] two clocks later.
    check_q_low_nibble_loads_data1: assert property (
        @(posedge clk) disable iff (!reset)
        (($past(reset, 1) == 1'b1) &&
         ($past(reset, 2) == 1'b1) &&
         ($past(select, 2) == 1'b1) &&
         ($past(sel, 2) == 3'b001))
        |-> (q[3:0] == $past(data1, 2))
    );

    // sel=010 loads data2 into q[3:0] two clocks later.
    check_q_low_nibble_loads_data2: assert property (
        @(posedge clk) disable iff (!reset)
        (($past(reset, 1) == 1'b1) &&
         ($past(reset, 2) == 1'b1) &&
         ($past(select, 2) == 1'b1) &&
         ($past(sel, 2) == 3'b010))
        |-> (q[3:0] == $past(data2, 2))
    );

    // sel=011 loads data3 into q[3:0] two clocks later.
    check_q_low_nibble_loads_data3: assert property (
        @(posedge clk) disable iff (!reset)
        (($past(reset, 1) == 1'b1) &&
         ($past(reset, 2) == 1'b1) &&
         ($past(select, 2) == 1'b1) &&
         ($past(sel, 2) == 3'b011))
        |-> (q[3:0] == $past(data3, 2))
    );

    // sel=100 loads data4 into q[3:0] two clocks later.
    check_q_low_nibble_loads_data4: assert property (
        @(posedge clk) disable iff (!reset)
        (($past(reset, 1) == 1'b1) &&
         ($past(reset, 2) == 1'b1) &&
         ($past(select, 2) == 1'b1) &&
         ($past(sel, 2) == 3'b100))
        |-> (q[3:0] == $past(data4, 2))
    );

    // sel=101 loads data5 into q[3:0] two clocks later.
    check_q_low_nibble_loads_data5: assert property (
        @(posedge clk) disable iff (!reset)
        (($past(reset, 1) == 1'b1) &&
         ($past(reset, 2) == 1'b1) &&
         ($past(select, 2) == 1'b1) &&
         ($past(sel, 2) == 3'b101))
        |-> (q[3:0] == $past(data5, 2))
    );

    // Invalid sel values load zero into q[3:0] two clocks later.
    check_q_low_nibble_loads_default_zero: assert property (
        @(posedge clk) disable iff (!reset)
        (($past(reset, 1) == 1'b1) &&
         ($past(reset, 2) == 1'b1) &&
         ($past(select, 2) == 1'b1) &&
         (($past(sel, 2) == 3'b110) || ($past(sel, 2) == 3'b111)))
        |-> (q[3:0] == 4'b0000)
    );

endmodule