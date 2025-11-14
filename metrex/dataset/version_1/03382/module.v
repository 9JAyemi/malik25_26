
module shift_register (
    input wire clk,
    input wire [3:0] inp,
    output wire [15:0] arr_out
);

    reg [15:0] arr;

    assign arr_out = {arr[15:4], inp[3:0]};

    always @(posedge clk) begin
        arr <= {arr[14:0], inp[3]}; 
    end

endmodule