// SVA checker for wavelet_transform
module wavelet_transform_sva #(
  parameter int n = 8,
  parameter int m = 8,
  parameter int k = 4
) (
  input  logic                  clk,
  input  logic        [n-1:0]   in,
  input  logic        [m-1:0]   out,
  input  logic signed [n-1:0]   input_samples,
  input  logic signed [m-1:0]   output_samples,
  input  logic signed [k-1:0]   h0,
  input  logic signed [k-1:0]   h1
);

  // Elaboration-time sanity checks
  initial begin
    assert (m % 2 == 0)
      else $error("wavelet_transform: parameter m must be even (loop writes i and i+1).");
    assert (n > 0 && m > 0 && k > 0)
      else $error("wavelet_transform: parameters n,m,k must be > 0.");
  end

  // Bit-accurate combinational model matching the DUT as coded
  function automatic logic [m-1:0] model_out
    (input logic [n-1:0] s, input logic [k-1:0] a0, input logic [k-1:0] a1);
    logic [m-1:0] r;
    int ii, jj;
    r = '0;
    for (ii = 0; ii < m; ii += 2) begin
      if (ii+1 < m) begin
        for (jj = 0; jj < k; jj++) begin
          if (ii+jj < n) begin
            // 1-bit MAC as in DUT: sum on 1-bit accumulators => XOR of ANDs
            r[ii]   = r[ii]   ^ (a0[jj] & s[ii+jj]);
            r[ii+1] = r[ii+1] ^ (a1[jj] & s[ii+jj]);
          end
        end
      end
    end
    return r;
  endfunction

  // Inputs/coefficients must be known when sampled; outputs must be known always
  assert property (@(posedge clk) !$isunknown(in)) else $error("X/Z on 'in' at sample.");
  assert property (@(posedge clk) !$isunknown(h0) && !$isunknown(h1)) else $error("X/Z on coefficients.");
  assert (!$isunknown(out)) else $error("X/Z on 'out'.");

  // Registered input sampling correctness
  assert property (@(posedge clk) input_samples == $past(in))
    else $error("input_samples does not match sampled 'in'.");

  // Out is a pure combinational function of current input_samples and taps
  // Using a clockless property so it rechecks on any change
  assert property (out == model_out(input_samples, h0, h1))
    else $error("Combinational mismatch: out != model_out(input_samples,h0,h1).");

  // Out mirrors internal output_samples net
  assert property (out == output_samples)
    else $error("out != output_samples (connectivity).");

  // Out should be stable between clock rising edges (only changes when input_samples updates)
  assert property (@(negedge clk) 1 |-> $stable(out) until_with $rose(clk))
    else $error("out changed between clock edges.");

  // Coverage: activity and both branches (even/odd outputs)
  cover property (@(posedge clk) $changed(out));
  cover property (@(posedge clk) $changed(out[0]));
  cover property (@(posedge clk) $changed(out[1]));
  cover property (@(posedge clk) out == '0);
  cover property (@(posedge clk) out != '0);

endmodule

// Bind into the DUT (connect internal regs for stronger checks)
bind wavelet_transform wavelet_transform_sva #(.n(n), .m(m), .k(k)) sva_i (
  .clk(clk),
  .in(in),
  .out(out),
  .input_samples(input_samples),
  .output_samples(output_samples),
  .h0(h0),
  .h1(h1)
);