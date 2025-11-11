
module mux_256to1 #(parameter DATA_WIDTH = 3) (
    input [DATA_WIDTH*256-1:0] data_in,
    input [8:0] sel,
    output reg [DATA_WIDTH-1:0] out
);

always @(*) begin
    out <= data_in[(sel+1)*DATA_WIDTH-1 : sel*DATA_WIDTH];
end

endmodule