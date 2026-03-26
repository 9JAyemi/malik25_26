module HilbertTransform #(
  parameter n = 4
) (
  input signed [n-1:0] in_real,
  output signed [n-1:0] out_imag
);


// Hilbert Transform function
function [n-1:0] hilbert_transform;
  input signed [n-1:0] x;
  integer i;
  begin
    for (i = 0; i < n; i = i + 2) begin
      hilbert_transform[i] = 0;
      hilbert_transform[i+1] = x[i] - x[i+1];
    end
  end
endfunction

assign out_imag = hilbert_transform(in_real);

endmodule