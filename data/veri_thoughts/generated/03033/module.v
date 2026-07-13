
module dual_edge_ff(input clk, input reset, input d, input select, output reg q);
    reg [1:0] ff_out;
    wire select_ff = select ? ff_out[1] : ff_out[0];

    always @(posedge clk) begin
        if (reset) begin
            ff_out <= 2'b0;
        end else begin
            ff_out <= {ff_out[0], d};
        end
    end

    always @(negedge clk) begin
        q <= select_ff;
    end
endmodule