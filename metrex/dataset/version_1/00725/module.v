
module clk_divider #
    (
        parameter DIVIDER = 15
    )
    (
        input IN_SIG,
        output wire OUT_SIG
    );

    function integer clogb2 (input integer bit_depth);
      begin
        for(clogb2=0; bit_depth>0; clogb2=clogb2+1)
          bit_depth = bit_depth >> 1;
      end
    endfunction

    localparam BITS = clogb2(DIVIDER-1);

    localparam MAX = 1 << BITS;

    localparam integer HIGH = DIVIDER / 2;

    reg [BITS:0] counter = 0;

    always @(posedge IN_SIG)
    begin
        counter = counter + 1;
        if (counter >= DIVIDER) begin
            counter = 0;
        end
    end

    assign OUT_SIG = (counter <= HIGH);

endmodule
