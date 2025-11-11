


module sky130_fd_sc_ms__nor2b (
    Y  ,
    A  ,
    B_N
);

    output Y  ;
    input  A  ;
    input  B_N;

    wire not0_out  ;
    wire and0_out_Y;

    not not0 (not0_out  , A              );
    and and0 (and0_out_Y, not0_out, B_N  );
    buf buf0 (Y         , and0_out_Y     );

endmodule
