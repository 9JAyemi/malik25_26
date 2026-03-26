module clock_divider(
    input clk_50,
    output reg clk_1
);

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    reg [31:0] counter = 0;

    always @(posedge clk_50) begin
        counter <= counter + 1;
        if (counter == 50000000) begin
            counter <= 0;
            clk_1 <= ~clk_1;
        end
    end

endmodule