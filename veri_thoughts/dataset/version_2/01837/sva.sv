module shiftReg_sva #(
    parameter int WIDTH = 8,
    parameter int ADDR_WIDTH = 2,
    parameter int DEPTH = 4
) (
    input logic clk,
    input logic [WIDTH-1:0] data,
    input logic ce,
    input logic [ADDR_WIDTH-1:0] a,
    input logic [WIDTH-1:0] q
);

    // Constrain address to valid range of the SRL depth.
    assume_valid_addr_range: assume property (
        @(posedge clk) a < DEPTH
    );

    // If CE was LOW last cycle and address is unchanged, q must hold its value.
    check_q_hold_when_prev_ce_low_and_a_stable: assert property (
        @(posedge clk) (!$past(ce) && (a == $past(a))) |-> (q == $past(q))
    );

    // When selecting stage 0, after a CE pulse last cycle q equals last cycle's data.
    check_stage0_data_latency: assert property (
        @(posedge clk) ($past(ce) && (a == '0)) |-> (q == $past(data))
    );

    // When selecting stage 1, after two consecutive CE pulses q equals data from 2 cycles ago.
    check_stage1_data_latency: assert property (
        @(posedge clk) ($past(ce,2) && $past(ce,1) && (a == 'd1)) |-> (q == $past(data,2))
    );

    // When selecting stage 2, after three consecutive CE pulses q equals data from 3 cycles ago.
    check_stage2_data_latency: assert property (
        @(posedge clk) ($past(ce,3) && $past(ce,2) && $past(ce,1) && (a == 'd2)) |-> (q == $past(data,3))
    );

    // When selecting stage 3, after four consecutive CE pulses q equals data from 4 cycles ago.
    check_stage3_data_latency: assert property (
        @(posedge clk) ($past(ce,4) && $past(ce,3) && $past(ce,2) && $past(ce,1) && (a == 'd3)) |-> (q == $past(data,4))
    );

    // If address increments by 1 and CE was HIGH last cycle, q must equal its previous value.
    check_q_preserved_on_addr_inc_with_prev_ce_high: assert property (
        @(posedge clk) ($past(ce) && ($past(a) < (DEPTH-1)) && (a == ($past(a) + 1))) |-> (q == $past(q))
    );

    // If address changes from 1 to 0 and CE was HIGH last cycle, q equals last cycle's data.
    check_addr_dec_to_zero_returns_prev_data: assert property (
        @(posedge clk) ($past(ce) && ($past(a) == 'd1) && (a == 'd0)) |-> (q == $past(data))
    );

endmodule