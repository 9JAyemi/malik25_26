module my_module_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic VPWR,
    input logic VGND,
    input logic Y
);
    // X implements NOR of A1 and A2 (sampled after inputs settle).
    check_x_is_nor_a1a2: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1 or
          posedge VPWR or negedge VPWR or
          posedge VGND or negedge VGND)
        (!$isunknown({A1, A2})) |-> ##0 (X === ~(A1 | A2))
    );

    // Y buffers X (sampled after drivers settle).
    check_y_buffers_x: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge X  or negedge X  or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1 or
          posedge VPWR or negedge VPWR or
          posedge VGND or negedge VGND)
        (!$isunknown(X)) |-> ##0 (Y === X)
    );

    // When X rises, Y must be HIGH after propagation.
    buf_y_high_on_x_rise: assert property (
        @(posedge X) ##0 (Y === 1'b1)
    );

    // When X falls, Y must be LOW after propagation.
    buf_y_low_on_x_fall: assert property (
        @(negedge X) ##0 (Y === 1'b0)
    );

    // When Y rises, X must be HIGH (consistency with Y=X).
    buf_x_high_on_y_rise: assert property (
        @(posedge Y) ##0 (X === 1'b1)
    );

    // When Y falls, X must be LOW (consistency with Y=X).
    buf_x_low_on_y_fall: assert property (
        @(negedge Y) ##0 (X === 1'b0)
    );
endmodule