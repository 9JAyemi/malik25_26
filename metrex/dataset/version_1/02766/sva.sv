// SVA for ecc_dec_fix
// Bind-friendly, concise, high-signal-coverage

module ecc_dec_fix_sva #(
  parameter TCQ = 100,
  parameter PAYLOAD_WIDTH = 64,
  parameter CODE_WIDTH = 72,
  parameter DATA_WIDTH = 64,
  parameter DQ_WIDTH = 72,
  parameter ECC_WIDTH = 8,
  parameter nCK_PER_CLK = 4
)(
  input logic clk,
  input logic rst,
  input logic [CODE_WIDTH*ECC_WIDTH-1:0] h_rows,
  input logic [2*nCK_PER_CLK*DQ_WIDTH-1:0] phy_rddata,
  input logic correct_en,
  input logic ecc_status_valid,
  input logic [2*nCK_PER_CLK*PAYLOAD_WIDTH-1:0] rd_data,
  input logic [2*nCK_PER_CLK-1:0] ecc_single,
  input logic [2*nCK_PER_CLK-1:0] ecc_multiple
);
  // The following internal signals are referenced by name from the bound DUT:
  // syndrome_r, ecc_rddata_r, flip_bits, h_matrix

  localparam int WORDS = 2*nCK_PER_CLK;
  localparam int RAW_BIT_WIDTH = PAYLOAD_WIDTH - DATA_WIDTH;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // 1) Pipeline correctness: syndrome_r is registered version of syndrome_ns(phy_rddata,h_rows)
  genvar k, m;
  generate
    for (k=0; k<WORDS; k++) begin : g_syn
      for (m=0; m<ECC_WIDTH; m++) begin : g_synb
        // syndrome_r[k,m] == ^(past(phy_word)&past(h_row))
        assert property (
          syndrome_r[k*ECC_WIDTH+m]
          == ^($past(phy_rddata[k*DQ_WIDTH +: CODE_WIDTH]) & $past(h_rows[m*CODE_WIDTH +: CODE_WIDTH]))
        ) else $error("syndrome_r mismatch at word %0d bit %0d", k, m);
      end
    end
  endgenerate

  // 2) Payload extraction pipeline correctness
  genvar i;
  generate
    for (i=0; i<WORDS; i++) begin : g_data_pipe
      assert property (
        ecc_rddata_r[i*PAYLOAD_WIDTH +: PAYLOAD_WIDTH]
        == $past(phy_rddata[i*DQ_WIDTH +: PAYLOAD_WIDTH])
      ) else $error("ecc_rddata_r mismatch at word %0d", i);
    end
  endgenerate

  // 3) Status generation correctness and mutual exclusion
  genvar v;
  generate
    for (v=0; v<WORDS; v++) begin : g_status
      wire [ECC_WIDTH-1:0] synd = syndrome_r[v*ECC_WIDTH +: ECC_WIDTH];
      assert property ((!ecc_status_valid) |-> (!ecc_single[v] && !ecc_multiple[v]))
        else $error("Status not gated by ecc_status_valid at word %0d", v);
      assert property ((ecc_status_valid && (synd=='0)) |-> (!ecc_single[v] && !ecc_multiple[v]))
        else $error("Non-zero status on zero syndrome at word %0d", v);
      assert property ((ecc_status_valid && (synd!='0) && (^synd)) |-> (ecc_single[v] && !ecc_multiple[v]))
        else $error("ecc_single wrong at word %0d", v);
      assert property ((ecc_status_valid && (synd!='0) && !(^synd)) |-> (!ecc_single[v] && ecc_multiple[v]))
        else $error("ecc_multiple wrong at word %0d", v);
      assert property (!(ecc_single[v] && ecc_multiple[v]))
        else $error("ecc_single and ecc_multiple both 1 at word %0d", v);

      // For single-error status, at most one data bit flips (0 allowed for parity-only error)
      assert property ((ecc_status_valid && ecc_single[v]) |-> $onehot0(flip_bits[v*DATA_WIDTH +: DATA_WIDTH]))
        else $error("Non onehot flip mask for single-error at word %0d", v);
    end
  endgenerate

  // 4) Data correction mapping (payload) and raw-bit passthrough
  genvar s;
  generate
    for (s=0; s= s+1) begin : g_map_dummy end // placeholder to avoid zero-iteration generate when WORDS==0
  endgenerate
  generate
    for (s=0; s<WORDS; s++) begin : g_map
      assert property (
        rd_data[s*PAYLOAD_WIDTH +: DATA_WIDTH]
        == (ecc_rddata_r[s*PAYLOAD_WIDTH +: DATA_WIDTH]
            ^ (correct_en ? flip_bits[s*DATA_WIDTH +: DATA_WIDTH] : '0))
      ) else $error("rd_data payload incorrect at word %0d", s);

      if (RAW_BIT_WIDTH > 0) begin : g_raw
        assert property (
          rd_data[(s+1)*PAYLOAD_WIDTH-1 -: RAW_BIT_WIDTH]
          == ecc_rddata_r[(s+1)*PAYLOAD_WIDTH-1 -: RAW_BIT_WIDTH]
        ) else $error("rd_data raw bits incorrect at word %0d", s);
      end
    end
  endgenerate

  // 5) H-matrix sanity (columns for data bits are non-zero and unique)
  genvar r1, r2;
  generate
    for (r1=0; r1<DATA_WIDTH; r1++) begin : g_h_nonzero
      assert property (h_matrix[r1] != '0)
        else $error("H-matrix column %0d is zero", r1);
    end
    for (r1=0; r1<DATA_WIDTH; r1++) begin : g_h_unique_1
      for (r2=r1+1; r2<DATA_WIDTH; r2++) begin : g_h_unique_2
        assert property (h_matrix[r1] != h_matrix[r2])
          else $error("H-matrix columns %0d and %0d are equal", r1, r2);
      end
    end
  endgenerate

  // 6) Basic X-check on outputs
  assert property (!$isunknown({ecc_single, ecc_multiple, rd_data})))
    else $error("Unknowns detected on outputs");

  // 7) Compact functional coverage
  generate
    for (v=0; v<WORDS; v++) begin : g_cov
      wire [ECC_WIDTH-1:0] synd = syndrome_r[v*ECC_WIDTH +: ECC_WIDTH];
      cover property (ecc_status_valid && (synd=='0)); // clean
      cover property (ecc_status_valid && (synd!='0) && (^synd) && (|flip_bits[v*DATA_WIDTH +: DATA_WIDTH]) && correct_en); // single, data corrected
      cover property (ecc_status_valid && (synd!='0) && (^synd) && !(|flip_bits[v*DATA_WIDTH +: DATA_WIDTH])); // single, parity-only
      cover property (ecc_status_valid && (synd!='0) && !(^synd)); // multiple
      cover property (correct_en==0); // correction disabled
    end
  endgenerate

endmodule

// Bind example:
// bind ecc_dec_fix ecc_dec_fix_sva #(
//   .TCQ(TCQ), .PAYLOAD_WIDTH(PAYLOAD_WIDTH), .CODE_WIDTH(CODE_WIDTH),
//   .DATA_WIDTH(DATA_WIDTH), .DQ_WIDTH(DQ_WIDTH), .ECC_WIDTH(ECC_WIDTH),
//   .nCK_PER_CLK(nCK_PER_CLK)
// ) ecc_dec_fix_sva_i (.*);