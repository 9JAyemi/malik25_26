// SVA checker for module 'parity'
// Bind this to the DUT:  bind parity parity_sva #(.n(n)) u_parity_sva (.*);

module parity_sva #(parameter int n = 8)
(
  input  logic [n-1:0] data,
  input  logic         sel,
  input  logic         parity,
  input  logic [n:0]   out
);

  // 1-hot for LSB (width-n)
  localparam logic [n-1:0] LSB_ONE = {{(n-1){1'b0}}, 1'b1};

  // Assertions (combinational, X-safe)
  always_comb begin
    // If inputs are known, outputs must be known
    if (!$isunknown({data, sel})) begin
      assert (!$isunknown({parity, out}))
        else $error("parity/out contain X/Z for known inputs");
    end

    // Parity bit must be the reduction XOR of data in all modes
    if (!$isunknown(data)) begin
      assert (parity === (^data))
        else $error("parity != ^data");
    end

    // Generator mode (sel==0): out == {data, parity}
    if (!$isunknown({data, sel}) && (sel == 1'b0)) begin
      assert (out[n:1] == data)
        else $error("GEN: out[n:1] != data");
      assert (out[0] == parity)
        else $error("GEN: out[0] != parity");
    end

    // Checker mode (sel==1):
    // - out[n] must be 0 (due to width extension in RHS assignments)
    // - if ^data==0: pass-through
    // - if ^data==1: flip LSB of data
    if (!$isunknown({data, sel}) && (sel == 1'b1)) begin
      assert (out[n] == 1'b0)
        else $error("CHK: out[n] must be 0");
      if ((^data) == 1'b0) begin
        assert (out[n-1:0] == data)
          else $error("CHK even: out != data");
      end
      else begin
        assert (out[n-1:0] == (data ^ LSB_ONE))
          else $error("CHK odd: out != data ^ 1");
      end
      // Resulting low n bits must have even parity
      assert ((^out[n-1:0]) == 1'b0)
        else $error("CHK: corrected data must have even parity");
    end
  end

  // Minimal functional coverage
  // Generator, even parity
  cover property ( (sel==1'b0) && ((^data)==1'b0) && (parity==1'b0) && (out==={data,1'b0}) );
  // Generator, odd parity
  cover property ( (sel==1'b0) && ((^data)==1'b1) && (parity==1'b1) && (out==={data,1'b1}) );
  // Checker, even: passthrough with MSB 0
  cover property ( (sel==1'b1) && ((^data)==1'b0) && (parity==1'b0) && (out==={1'b0,data}) );
  // Checker, odd: LSB flipped with MSB 0
  cover property ( (sel==1'b1) && ((^data)==1'b1) && (parity==1'b1) && (out==={1'b0,(data ^ LSB_ONE)}) );

endmodule

// Bind example (place in a package or a testbench file):
// bind parity parity_sva #(.n(n)) u_parity_sva (.*);