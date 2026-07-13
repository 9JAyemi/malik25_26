


module sky130_fd_sc_hd__lpflow_inputiso0n (
    X      ,
    A      ,
    SLEEP_B
);

    output X      ;
    input  A      ;
    input  SLEEP_B;

    and and0 (X     , A, SLEEP_B     );

endmodule
