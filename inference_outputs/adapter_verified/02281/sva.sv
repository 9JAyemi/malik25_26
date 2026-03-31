module mux_priority_encoder_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel_b1,
    input logic sel_b2,
    input logic [7:0] in,
    input logic [2:0] pos,
    input logic [3:0] out_sum
);

// pos must match the implemented priority encoder.
    check_pos_encoding: assert property (
        @(posedge clk) pos == (in[7] ? 3'd7 :
                               in[6] ? 3'd6 :
                               in[5] ? 3'd5 :
                               in[4] ? 3'd4 :
                               in[3] ? 3'd3 :
                               in[2] ? 3'd2 :
                               in[1] ? 3'd1 :
                               in[0] ? 3'd0 : 3'd0)
    );

// out_sum must match the implemented mux and positional addition.
    check_out_sum_function: assert property (
        @(posedge clk)
        out_sum == ((sel_b1 & sel_b2) ? (b + pos) :
                    ((sel_b1 | sel_b2) ? (a + pos) : 4'd0))
    );

// When both select inputs are high, b is selected and pos is added.
    check_select_b_path: assert property (
        @(posedge clk) (sel_b1 && sel_b2) |-> (out_sum == (b + pos))
    );

// When either select input is high, a is selected and pos is added.
    check_select_a_path: assert property (
        @(posedge clk) (sel_b1 || sel_b2) |-> (out_sum == (a + pos))
    );

// When both select inputs are low, the output is zero.
    check_no_select_path: assert property (
        @(posedge clk) !(sel_b1 || sel_b2) |-> (out_sum == 4'd0)
    );

// When the input bit at pos is high, pos must be that bit index.
    check_pos_matches_first_high_bit: assert property (
        @(posedge clk) in[pos] |-> (pos == (in[7:0] - 8'd1))
    );

// When no input bit is high, pos must be zero.
    check_pos_zero_when_no_high_bit: assert property (
        @(posedge clk) !in[7:0] |-> (pos == 3'd0)
    );

// When only the LSB is high, pos must be zero.
    check_pos_zero_when_only_lsb: assert property (
        @(posedge clk) (in == 8'h01) |-> (pos == 3'd0)
    );

// When only the MSB is high, pos must be seven.
    check_pos_seven_when_only_msb: assert property (
        @(posedge clk) (in == 8'h80) |-> (pos == 3'd7)
    );

endmodule
