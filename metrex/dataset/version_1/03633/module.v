
module binary_search (
    input [15:0] array, // Assuming 8 2-bit elements packed into a 16-bit vector
    input [1:0] search_key, // Adjusting search_key width to match array element width
    output reg [2:0] index // 3 bits wide to represent indexes 0-7 or an invalid index
);

    parameter N = 8; // Number of array elements

    integer i;
    reg found;

    always @(*) begin
        index = N; // Initializing index to invalid value
        found = 0;
        for (i = 0; i < N; i = i + 1) begin 
            if (array[(i*2)+:2] == search_key) begin // Slicing array to match 2-bit elements
                index = i;
                found = 1;
            end
        end
    end

endmodule