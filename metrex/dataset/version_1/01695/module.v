
module sky130_fd_sc_hs__einvn (
    A   ,
    TE_B,
    Z
);

    input  A   ; // input A
    input  TE_B; // tri-state enable 
    output Z   ; // output 

    assign Z = (TE_B) ? ~A : A; //tri-state enabled

endmodule