module parity_calculator(
    input [15:0] data,
    output parity
);

    wire [7:0] data_low;
    wire [7:0] data_high;
    wire [3:0] parity_low;
    wire [3:0] parity_high;
    wire parity_odd;

    // Split the input data into two 8-bit parts
    assign data_low = data[7:0];
    assign data_high = data[15:8];

    // Calculate the parity for each 8-bit part
    assign parity_low = {data_low[0], data_low[1], data_low[2], data_low[3]} ^ {data_low[4], data_low[5], data_low[6], data_low[7]};
    assign parity_high = {data_high[0], data_high[1], data_high[2], data_high[3]} ^ {data_high[4], data_high[5], data_high[6], data_high[7]};

    // Calculate the parity for the entire 16-bit input data
    assign parity_odd = parity_low[0] ^ parity_low[1] ^ parity_low[2] ^ parity_low[3] ^ parity_high[0] ^ parity_high[1] ^ parity_high[2] ^ parity_high[3];

    // Set the parity bit to 1 if the number of 1's in the input data is odd, and 0 if it is even
    assign parity = (parity_odd == 1'b1) ? 1'b1 : 1'b0;

endmodule