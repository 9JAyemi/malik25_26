module dff_sscan_sva #(
    parameter SIZE = 1
) (
    input  logic [SIZE-1:0] din,
    input  logic            clk,
    input  logic [SIZE-1:0] q,
    input  logic            se,
    input  logic [SIZE-1:0] si,
    input  logic [SIZE-1:0] so
);

`ifdef CONNECT_SHADOW_SCAN
    // q captures si when scan is enabled.
    check_q_captures_scan_input: assert property (
        @(posedge clk) se |=> (q == $past(si))
    );

    // q captures din when scan is disabled.
    check_q_captures_functional_input: assert property (
        @(posedge clk) !se |=> (q == $past(din))
    );

    // so mirrors q when shadow scan is connected.
    check_so_mirrors_q: assert property (
        @(posedge clk) (so == q)
    );
`else
    // q captures din on every rising clock edge.
    check_q_captures_din: assert property (
        @(posedge clk) 1'b1 |=> (q == $past(din))
    );

    // Scan enable does not change the captured source when scan is disconnected.
    check_q_ignores_scan_enable: assert property (
        @(posedge clk) se |=> (q == $past(din))
    );

    // so is tied low when shadow scan is not connected.
    check_so_tied_low: assert property (
        @(posedge clk) (so == {SIZE{1'b0}})
    );
`endif

endmodule