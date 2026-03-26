module arduino_switch_analog_bit_sva (
    input logic       clk,
    input logic [1:0] gpio_sel,
    input logic       tri_i_out,
    input logic       tri_o_out,
    input logic       tri_t_out,
    input logic       tri_i_in,
    input logic       tri_o_in,
    input logic       tri_t_in,
    input logic       sda_i_in,
    input logic       sda_o_in,
    input logic       sda_t_in,
    input logic       scl_i_in,
    input logic       scl_o_in,
    input logic       scl_t_in
);

    // tri_o_out follows tri_o_in when gpio_sel is 0 or 1.
    check_tri_o_out_sel01: assert property (
        @(posedge clk)
        ((gpio_sel == 2'h0) || (gpio_sel == 2'h1)) |-> (tri_o_out == tri_o_in)
    );

    // tri_o_out follows sda_o_in when gpio_sel is 2.
    check_tri_o_out_sel2: assert property (
        @(posedge clk)
        (gpio_sel == 2'h2) |-> (tri_o_out == sda_o_in)
    );

    // tri_o_out follows scl_o_in when gpio_sel is 3.
    check_tri_o_out_sel3: assert property (
        @(posedge clk)
        (gpio_sel == 2'h3) |-> (tri_o_out == scl_o_in)
    );

    // tri_t_out follows tri_t_in when gpio_sel is 0 or 1.
    check_tri_t_out_sel01: assert property (
        @(posedge clk)
        ((gpio_sel == 2'h0) || (gpio_sel == 2'h1)) |-> (tri_t_out == tri_t_in)
    );

    // tri_t_out follows sda_t_in when gpio_sel is 2.
    check_tri_t_out_sel2: assert property (
        @(posedge clk)
        (gpio_sel == 2'h2) |-> (tri_t_out == sda_t_in)
    );

    // tri_t_out follows scl_t_in when gpio_sel is 3.
    check_tri_t_out_sel3: assert property (
        @(posedge clk)
        (gpio_sel == 2'h3) |-> (tri_t_out == scl_t_in)
    );

    // tri_i_out is routed to tri_i_in only when gpio_sel is 0 or 1.
    check_tri_i_demux_sel01: assert property (
        @(posedge clk)
        ((gpio_sel == 2'h0) || (gpio_sel == 2'h1)) |-> ({scl_i_in, sda_i_in, tri_i_in} == {1'b0, 1'b0, tri_i_out})
    );

    // tri_i_out is routed to sda_i_in only when gpio_sel is 2.
    check_tri_i_demux_sel2: assert property (
        @(posedge clk)
        (gpio_sel == 2'h2) |-> ({scl_i_in, sda_i_in, tri_i_in} == {1'b0, tri_i_out, 1'b0})
    );

    // tri_i_out is routed to scl_i_in only when gpio_sel is 3.
    check_tri_i_demux_sel3: assert property (
        @(posedge clk)
        (gpio_sel == 2'h3) |-> ({scl_i_in, sda_i_in, tri_i_in} == {tri_i_out, 1'b0, 1'b0})
    );

endmodule