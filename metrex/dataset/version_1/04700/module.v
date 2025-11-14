
module min_finder (
    input [7:0] a, b, c, d,
    output [7:0] min);

    wire [1:0] encoded;
    wire [3:0] inputs;

    // Instantiating a 4-to-2 priority encoder
    priority_encoder pe(.encoded(encoded), .inputs(inputs));

    // Extracting the 4 least significant bits from each 8-bit input
    assign inputs = {a[3:0], b[3:0], c[3:0], d[3:0]};

    // Instantiating a 2-to-4 decoder
    decoder dec(.decoded(min), .encoded(encoded));

endmodule
module priority_encoder (
    output reg [1:0] encoded,
    input [3:0] inputs);

    always @* begin
        encoded = 2'd0;
        if (inputs[0] <= inputs[1] && inputs[0] <= inputs[2] && inputs[0] <= inputs[3])
            encoded = 2'b01;
        else if (inputs[1] <= inputs[2] && inputs[1] <= inputs[3])
            encoded = 2'b10;
        else if (inputs[2] <= inputs[3])
            encoded = 2'b11;
    end

endmodule
module decoder (
    output [7:0] decoded,
    input [1:0] encoded);

    assign decoded = (encoded == 2'b01) ? 8'b0000_0001 :
                    (encoded == 2'b10) ? 8'b0000_0010 :
                    (encoded == 2'b11) ? 8'b0000_0100 : 8'b0000_0000;

endmodule