module mux4to1_assertions (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C,
    input logic [3:0] D,
    input logic [1:0] S,
    input logic clk,
    input logic [3:0] Y
);

    // Y matches the input selected on the previous rising clock edge.
    check_registered_mux_function: assert property (
        @(posedge clk)
        1'b1 |=> (
            (($past(S) == 2'b00) && (Y == $past(A))) ||
            (($past(S) == 2'b01) && (Y == $past(B))) ||
            (($past(S) == 2'b10) && (Y == $past(C))) ||
            (($past(S) == 2'b11) && (Y == $past(D)))
        )
    );

    // Selecting A loads A into Y on the next sampled cycle.
    check_select_a_updates_y: assert property (
        @(posedge clk)
        (S == 2'b00) |=> (Y == $past(A))
    );

    // Selecting B loads B into Y on the next sampled cycle.
    check_select_b_updates_y: assert property (
        @(posedge clk)
        (S == 2'b01) |=> (Y == $past(B))
    );

    // Selecting C loads C into Y on the next sampled cycle.
    check_select_c_updates_y: assert property (
        @(posedge clk)
        (S == 2'b10) |=> (Y == $past(C))
    );

    // Selecting D loads D into Y on the next sampled cycle.
    check_select_d_updates_y: assert property (
        @(posedge clk)
        (S == 2'b11) |=> (Y == $past(D))
    );

endmodule