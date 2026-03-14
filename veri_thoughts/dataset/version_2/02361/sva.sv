module sky130_fd_sc_ls__bufinv_sva (
    input logic A,
    input logic Y
);
    // On A rising, Y must be low (Y = ~A).
    y_low_on_a_rise: assert property (
        @(posedge A) (Y === 1'b0)
    );

    // On A falling, Y must be high (Y = ~A).
    y_high_on_a_fall: assert property (
        @(negedge A) (Y === 1'b1)
    );

    // When A rises, Y must fall.
    y_falls_when_a_rises: assert property (
        @(posedge A) $fell(Y)
    );

    // When A falls, Y must rise.
    y_rises_when_a_falls: assert property (
        @(negedge A) $rose(Y)
    );

    // On Y rising, A must be low (A = ~Y).
    a_low_on_y_rise: assert property (
        @(posedge Y) (A === 1'b0)
    );

    // On Y falling, A must be high (A = ~Y).
    a_high_on_y_fall: assert property (
        @(negedge Y) (A === 1'b1)
    );

    // When Y rises, A must fall.
    a_falls_when_y_rises: assert property (
        @(posedge Y) $fell(A)
    );

    // When Y falls, A must rise.
    a_rises_when_y_falls: assert property (
        @(negedge Y) $rose(A)
    );

    // On any transition of A or Y, Y must equal bitwise NOT of A.
    complement_on_any_transition: assert property (
        @(posedge A or negedge A or posedge Y or negedge Y) (Y === ~A)
    );
endmodule