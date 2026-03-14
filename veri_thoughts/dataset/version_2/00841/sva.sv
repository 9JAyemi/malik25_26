module top_module_sva (
    input logic clk,
    input logic rst_n,
    input logic write_en,
    input logic [7:0] write_addr,
    input logic [3:0] write_data,
    input logic read_en,
    input logic [7:0] read_addr,
    input logic [3:0] mux_in_0,
    input logic [3:0] mux_in_1,
    input logic [3:0] mux_in_2,
    input logic [3:0] mux_in_3,
    input logic [1:0] mux_sel,
    input logic [3:0] out
);
    // During reset, out must be cleared to 0.
    check_reset_clears_out: assert property (
        @(posedge clk) !rst_n |-> (out == 4'b0000)
    );

    // When read_en is LOW, out holds its previous value.
    check_out_holds_without_read: assert property (
        @(posedge clk) disable iff (!rst_n) (!read_en) |=> (out == $past(out))
    );

    // With read_en HIGH and mux_sel==01, out captures mux_in_0 on next cycle.
    check_read_sel_01_routes_mux_in_0: assert property (
        @(posedge clk) disable iff (!rst_n) (read_en && (mux_sel == 2'b01)) |=> (out == $past(mux_in_0))
    );

    // With read_en HIGH and mux_sel==10, out captures mux_in_1 on next cycle.
    check_read_sel_10_routes_mux_in_1: assert property (
        @(posedge clk) disable iff (!rst_n) (read_en && (mux_sel == 2'b10)) |=> (out == $past(mux_in_1))
    );

    // With read_en HIGH and mux_sel==11, out captures mux_in_2 on next cycle.
    check_read_sel_11_routes_mux_in_2: assert property (
        @(posedge clk) disable iff (!rst_n) (read_en && (mux_sel == 2'b11)) |=> (out == $past(mux_in_2))
    );
endmodule