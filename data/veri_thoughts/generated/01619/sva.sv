module connection_module_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic select,
    input logic w,
    input logic x,
    input logic y,
    input logic z
);
    // Note: No clock/reset in RTL; combinational connections sampled on any input/output edge.
    // Define a sampling event on any edge of DUT ports.
    localparam bit UNUSED = 1'b0; // prevent empty module warnings
    // Event expression used by all assertions
    `define ANY_EDGE_EVENT (posedge a or negedge a or \
                            posedge b or negedge b or \
                            posedge c or negedge c or \
                            posedge select or negedge select or \
                            posedge w or negedge w or \
                            posedge x or negedge x or \
                            posedge y or negedge y or \
                            posedge z or negedge z)

    // w must always equal a.
    check_w_equals_a: assert property (
        @(`ANY_EDGE_EVENT) (w == a)
    );

    // z must always equal c.
    check_z_equals_c: assert property (
        @(`ANY_EDGE_EVENT) (z == c)
    );

    // When select is 0, x must equal b.
    check_x_when_sel0: assert property (
        @(`ANY_EDGE_EVENT) (select == 1'b0) |-> (x == b)
    );

    // When select is 1, x must equal c.
    check_x_when_sel1: assert property (
        @(`ANY_EDGE_EVENT) (select == 1'b1) |-> (x == c)
    );

    // When select is 0, y must equal c.
    check_y_when_sel0: assert property (
        @(`ANY_EDGE_EVENT) (select == 1'b0) |-> (y == c)
    );

    // When select is 1, y must equal b.
    check_y_when_sel1: assert property (
        @(`ANY_EDGE_EVENT) (select == 1'b1) |-> (y == b)
    );

    // The pair {x,y} must be exactly {b,c}.
    check_xy_match_bc_set: assert property (
        @(`ANY_EDGE_EVENT) ((x == b) && (y == c)) || ((x == c) && (y == b))
    );

    // x equals y iff b equals c.
    check_xy_equality_reflects_bc: assert property (
        @(`ANY_EDGE_EVENT) ((x == y) == (b == c))
    );

    // When select is 1, x must equal z (both select c).
    check_x_equals_z_when_sel1: assert property (
        @(`ANY_EDGE_EVENT) (select == 1'b1) |-> (x == z)
    );

    // When select is 0, y must equal z (both select c).
    check_y_equals_z_when_sel0: assert property (
        @(`ANY_EDGE_EVENT) (select == 1'b0) |-> (y == z)
    );

endmodule