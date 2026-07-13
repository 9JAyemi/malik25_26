module cordic_stage_sva #(
    parameter int bitwidth = 16,
    parameter int zwidth   = 16,
    parameter int shift    = 1
) (
    input logic                 clock,
    input logic                 reset,
    input logic                 enable,
    input logic [bitwidth-1:0]  xi,
    input logic [bitwidth-1:0]  yi,
    input logic [zwidth-1:0]    zi,
    input logic [zwidth-1:0]    constant,
    input logic [bitwidth-1:0]  xo,
    input logic [bitwidth-1:0]  yo,
    input logic [zwidth-1:0]    zo
);

    // Reset clears all registered outputs.
    check_reset_clears_outputs: assert property (
        @(posedge clock) reset |=> (xo == '0) && (yo == '0) && (zo == '0)
    );

    // When zi sign bit is 0, xo subtracts shifted yi.
    check_xo_update_when_zi_sign_zero: assert property (
        @(posedge clock) disable iff (reset)
        (zi[zwidth-1] == 1'b0) |=> (
            xo == $past(xi - {{shift+1{yi[bitwidth-1]}}, yi[bitwidth-2:shift]})
        )
    );

    // When zi sign bit is 0, yo adds shifted xi.
    check_yo_update_when_zi_sign_zero: assert property (
        @(posedge clock) disable iff (reset)
        (zi[zwidth-1] == 1'b0) |=> (
            yo == $past(yi + {{shift+1{xi[bitwidth-1]}}, xi[bitwidth-2:shift]})
        )
    );

    // When zi sign bit is 0, zo subtracts constant.
    check_zo_update_when_zi_sign_zero: assert property (
        @(posedge clock) disable iff (reset)
        (zi[zwidth-1] == 1'b0) |=> (
            zo == $past(zi - constant)
        )
    );

    // When zi sign bit is 1, xo adds shifted yi.
    check_xo_update_when_zi_sign_one: assert property (
        @(posedge clock) disable iff (reset)
        (zi[zwidth-1] == 1'b1) |=> (
            xo == $past(xi + {{shift+1{yi[bitwidth-1]}}, yi[bitwidth-2:shift]})
        )
    );

    // When zi sign bit is 1, yo subtracts shifted xi.
    check_yo_update_when_zi_sign_one: assert property (
        @(posedge clock) disable iff (reset)
        (zi[zwidth-1] == 1'b1) |=> (
            yo == $past(yi - {{shift+1{xi[bitwidth-1]}}, xi[bitwidth-2:shift]})
        )
    );

    // When zi sign bit is 1, zo adds constant.
    check_zo_update_when_zi_sign_one: assert property (
        @(posedge clock) disable iff (reset)
        (zi[zwidth-1] == 1'b1) |=> (
            zo == $past(zi + constant)
        )
    );

endmodule