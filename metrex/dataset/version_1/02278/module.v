
module MISTRAL_FF(
    input DATAIN,
     input CLK,
    input ACLR, ENA, SCLR, SLOAD, SDATA,
    output reg Q
);

`ifdef cyclonev
specify
    if (ENA && ACLR !== 1'b0 && !SCLR && !SLOAD) (posedge CLK => (Q : DATAIN)) = 731;
    if (ENA && SCLR) (posedge CLK => (Q : 1'b0)) = 890;
    if (ENA && !SCLR && SLOAD) (posedge CLK => (Q : SDATA)) = 618;

    $setup(DATAIN, posedge CLK,  0);
    $setup(ENA, posedge CLK,  0);
    $setup(SCLR, posedge CLK,  0);
    $setup(SLOAD, posedge CLK,  0);
    $setup(SDATA, posedge CLK,  0);

    if (ACLR === 1'b0) (ACLR => Q) = 282;
endspecify
`endif
`ifdef cyclone10gx
specify
    if (ENA && ACLR !== 1'b0 && !SCLR && !SLOAD) (posedge CLK => (Q : DATAIN)) = 219;
    if (ENA && SCLR) (posedge CLK => (Q : 1'b0)) = 219;
    if (ENA && !SCLR && SLOAD) (posedge CLK => (Q : SDATA)) = 219;

    $setup(DATAIN, posedge CLK, 268);
    $setup(ENA, posedge CLK, 268);
    $setup(SCLR, posedge CLK, 268);
    $setup(SLOAD, posedge CLK, 268);
    $setup(SDATA, posedge CLK, 268);

    if (ACLR === 1'b0) (ACLR => Q) = 0;
endspecify
`endif

initial begin
    Q = 0;
end

always @(posedge CLK, negedge ACLR) begin
    if (!ACLR) Q <= 0;
    else if (ENA) begin
        if (SCLR) Q <= 0;
        else if (SLOAD) Q <= SDATA;
        else Q <= DATAIN;
    end
end

endmodule
