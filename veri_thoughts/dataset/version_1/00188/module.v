module and_gate(
    input in1,
    input in2,
    output out
);

reg subsig1 ;
reg subsig2 ;

assign out = in1 & in2;

`ifdef iverilog
   // stop icarus optimizing signals away
   wire redundant = subsig1 | subsig2;
`endif

endmodule