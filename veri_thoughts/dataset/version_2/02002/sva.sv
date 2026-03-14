module UART_Rx_sva (
    input logic CLK,
    input logic [7:0] D,
    input logic RD,
    input logic RST,
    input logic RX,
    input logic RXNE,
    input logic prev_CLK_B,
    input logic CLK_B,
    input logic [3:0] symbol,
    input logic [1:0] symbol_cnt,
    input logic busy,
    input logic [9:0] data,
    input logic [3:0] data_cnt
);
    // prev_CLK_B tracks the previous value of CLK_B.
    track_prev_clk_b: assert property (
        @(posedge CLK) disable iff (RST) prev_CLK_B == $past(CLK_B)
    );

    // Synchronous reset clears key registers on the next cycle.
    reset_clears_regs_next: assert property (
        @(posedge CLK) RST |=> (symbol_cnt == 2'd0) && (data_cnt == 4'd0) && (RXNE == 1'b0) && (busy == 1'b0) && (D == 8'h00)
    );

    // RD high clears RXNE on the next clock.
    rd_clears_rxne_next: assert property (
        @(posedge CLK) disable iff (RST) $past(RD) |-> (RXNE == 1'b0)
    );

    // RXNE can only fall due to RD.
    rxne_fall_only_on_rd: assert property (
        @(posedge CLK) disable iff (RST) $fell(RXNE) |-> $past(RD)
    );

    // Valid start condition (on CLK_B rise) sets busy and loads data_cnt=9, symbol_cnt=2.
    start_sets_busy_and_counters: assert property (
        @(posedge CLK) disable iff (RST)
            $past((CLK_B == 1'b1) && (prev_CLK_B == 1'b0) && (RX == 1'b0) && (symbol[3] == 1'b0) && (data_cnt == 4'd0) && (busy == 1'b0))
        |-> (busy == 1'b1) && (data_cnt == 4'd9) && (symbol_cnt == 2'd2)
    );

    // While busy and on CLK_B rise, nonzero symbol_cnt decrements by 1.
    symbol_cnt_counts_down: assert property (
        @(posedge CLK) disable iff (RST)
            $past((CLK_B == 1'b1) && (prev_CLK_B == 1'b0) && (busy == 1'b1) && (symbol_cnt != 2'd0))
        |-> (symbol_cnt == $past(symbol_cnt) - 2'd1)
    );

    // While busy and sampling (symbol_cnt==0), load symbol_cnt=3 and decrement data_cnt.
    load_symbol_cnt3_and_dec_data_cnt: assert property (
        @(posedge CLK) disable iff (RST)
            $past((CLK_B == 1'b1) && (prev_CLK_B == 1'b0) && (busy == 1'b1) && (symbol_cnt == 2'd0) && (data_cnt != 4'd0))
        |-> (symbol_cnt == 2'd3) && (data_cnt == $past(data_cnt) - 4'd1)
    );

    // End of frame (symbol_cnt==0 and data_cnt==0 on CLK_B rise) asserts RXNE and clears busy.
    end_of_frame_sets_rxne_and_clears_busy: assert property (
        @(posedge CLK) disable iff (RST)
            $past((CLK_B == 1'b1) && (prev_CLK_B == 1'b0) && (busy == 1'b1) && (symbol_cnt == 2'd0) && (data_cnt == 4'd0))
        |-> (RXNE == 1'b1) && (busy == 1'b0)
    );

    // On each CLK_B rise, shift in RX into the symbol register.
    symbol_shifts_on_clk_b_rise: assert property (
        @(posedge CLK) disable iff (RST)
            $past((CLK_B == 1'b1) && (prev_CLK_B == 1'b0))
        |-> (symbol == {$past(RX), $past(symbol[3:1])})
    );

    // On each sample (CLK_B rise with busy and symbol_cnt==0), data shifts right by 1.
    data_shifts_right_on_sample: assert property (
        @(posedge CLK) disable iff (RST)
            $past((CLK_B == 1'b1) && (prev_CLK_B == 1'b0) && (busy == 1'b1) && (symbol_cnt == 2'd0))
        |-> (data[8:0] == $past(data[9:1]))
    );

    // At end of frame, D is loaded from shifted data (old data[9:2]).
    D_loads_from_shifted_data: assert property (
        @(posedge CLK) disable iff (RST)
            $past((CLK_B == 1'b1) && (prev_CLK_B == 1'b0) && (busy == 1'b1) && (symbol_cnt == 2'd0) && (data_cnt == 4'd0))
        |-> (D == $past(data[9:2]))
    );

    // busy only rises on a valid start condition at a CLK_B rise.
    busy_rise_requires_start: assert property (
        @(posedge CLK) disable iff (RST)
            $rose(busy)
        |-> $past((CLK_B == 1'b1) && (prev_CLK_B == 1'b0) && (RX == 1'b0) && (symbol[3] == 1'b0) && (data_cnt == 4'd0) && (busy == 1'b0))
    );

    // busy only falls at end of frame on a CLK_B rise.
    busy_fall_requires_eof: assert property (
        @(posedge CLK) disable iff (RST)
            $fell(busy)
        |-> $past((CLK_B == 1'b1) && (prev_CLK_B == 1'b0) && (busy == 1'b1) && (symbol_cnt == 2'd0) && (data_cnt == 4'd0))
    );

    // While symbol_cnt!=0 on a CLK_B rise, data remains stable (no shift yet).
    data_stable_while_symbol_window: assert property (
        @(posedge CLK) disable iff (RST)
            $past((CLK_B == 1'b1) && (prev_CLK_B == 1'b0) && (busy == 1'b1) && (symbol_cnt != 2'd0))
        |-> (data == $past(data))
    );
endmodule