module input_buffer (
    input in,
    input en,
    output out
);

reg stored_out;
always @ (posedge en) begin
    if (en) begin
        stored_out <= in;
    end
end

assign out = en ? in : stored_out;

endmodule