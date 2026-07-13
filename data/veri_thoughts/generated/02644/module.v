module top_module (
    input A, B, C, D, // Inputs for priority encoder and multiplexer
    output reg [1:0] X, // Output from priority encoder
    output reg Y, // Output from priority encoder
    output reg Z // Output from multiplexer and functional module
);

// Priority encoder
always @ (A or B or C or D) begin
    if (A) begin
        X = 0;
        Y = 1;
    end else if (B) begin
        X = 1;
        Y = 1;
    end else if (C) begin
        X = 2;
        Y = 1;
    end else if (D) begin
        X = 3;
        Y = 1;
    end else begin
        X = 0;
        Y = 0;
    end
end

// Multiplexer
always @ (A or B or C or D) begin
    if (A) begin
        Z = A;
    end else if (B) begin
        Z = B;
    end else if (C) begin
        Z = C;
    end else if (D) begin
        Z = D;
    end else begin
        Z = 0;
    end
end

endmodule