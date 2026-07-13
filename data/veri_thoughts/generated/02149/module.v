

module BitLpf #(
    parameter FILT_BITS = 8
)
(
    input  clk,    input  rst,    input  en,     input  dataIn, output dataOut );

reg signed [FILT_BITS-1:0] filter;

assign dataOut = filter[FILT_BITS-1];

always @(posedge clk) begin
    if (rst) begin
        filter <= 'd0;
    end
    else if (en) begin
        filter <= filter + dataIn - dataOut;
    end
end

endmodule

