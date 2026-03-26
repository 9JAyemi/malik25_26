module blocking_cond_sva (
    input logic in,
    input logic out
);
    // No clocked assertions for this clockless combinational module.
endmodule

module uut_sva (
    input logic clk,
    input logic arst,
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic e,
    input logic f,
    input logic [3:0] out1
);

    function automatic logic [3:0] uut_a_path_next (
        input logic [3:0] prev_out1,
        input logic b_in,
        input logic c_in,
        input logic d_in,
        input logic e_in,
        input logic f_in
    );
        logic [3:0] tmp;
        begin
            tmp = prev_out1;
            case ({b_in, c_in})
                2'b00: tmp = tmp + 4'd9;
                2'b01, 2'b10: tmp = tmp + 4'd13;
                default: ;
            endcase
            if (d_in) begin
                tmp = tmp + 4'd2;
                tmp = tmp + 4'd1;
            end
            case ({e_in, f_in})
                2'b11: tmp = tmp + 4'd8;
                2'b00: ;
                default: tmp = tmp + 4'd10;
            endcase
            tmp = tmp ^ 4'd7;
            uut_a_path_next = tmp + 4'd14;
        end
    endfunction

    // Reset drives out1 to zero by the next sampled event.
    check_uut_reset_clears_out1: assert property (
        @(posedge clk or posedge arst) arst |=> (out1 == 4'd0)
    );

    // When a is low, the clocked update only adds 14.
    check_uut_no_a_path: assert property (
        @(posedge clk or posedge arst) disable iff (arst)
        (!$initstate && !a) |=> (out1 == ($past(out1) + 4'd14))
    );

    // When a is high, out1 follows the full blocking-assignment sequence.
    check_uut_a_path: assert property (
        @(posedge clk or posedge arst) disable iff (arst)
        (!$initstate && a) |=> (out1 == uut_a_path_next($past(out1), $past(b), $past(c), $past(d), $past(e), $past(f)))
    );

endmodule

module uart_sva (
    input logic reset,
    input logic txclk,
    input logic ld_tx_data,
    input logic tx_empty,
    input logic [3:0] tx_cnt
);

    // Reset sets the transmitter empty and clears the count.
    check_uart_reset_state: assert property (
        @(posedge txclk) reset |=> (tx_empty && (tx_cnt == 4'd0))
    );

    // Loading while idle clears tx_empty without incrementing tx_cnt that cycle.
    check_uart_idle_load_starts_busy: assert property (
        @(posedge txclk) disable iff (reset)
        (!$initstate && tx_empty && ld_tx_data) |=> ((!tx_empty) && (tx_cnt == $past(tx_cnt)))
    );

    // Staying idle without a load leaves tx_empty and tx_cnt unchanged.
    check_uart_idle_no_load_holds_state: assert property (
        @(posedge txclk) disable iff (reset)
        (!$initstate && tx_empty && !ld_tx_data) |=> (tx_empty && (tx_cnt == $past(tx_cnt)))
    );

    // Once busy, tx_empty remains low until reset.
    check_uart_busy_stays_busy: assert property (
        @(posedge txclk) disable iff (reset)
        (!$initstate && !tx_empty) |=> (!tx_empty)
    );

    // While busy, tx_cnt increments on each clock.
    check_uart_busy_increments_count: assert property (
        @(posedge txclk) disable iff (reset)
        (!$initstate && !tx_empty) |=> (tx_cnt == ($past(tx_cnt) + 4'd1))
    );

endmodule