// SVA bind modules for priority_encoder and gray_code_generator

// Assertions + coverage for priority_encoder
module priority_encoder_sva (
  input  logic [3:0] binary_in,
  input  logic [1:0] priority_out
);
  logic [1:0] exp_enc;
  always_comb begin
    exp_enc = binary_in[0] ? 2'b00 :
              binary_in[1] ? 2'b01 :
              binary_in[2] ? 2'b10 :
              binary_in[3] ? 2'b11 : 2'b00;

    assert (priority_out === exp_enc)
      else $error("priority_encoder mismatch bin=%b out=%b exp=%b", binary_in, priority_out, exp_enc);

    if (!$isunknown(binary_in))
      assert (!$isunknown(priority_out))
        else $error("priority_out X/Z with known input");

    // Functional coverage
    cover (binary_in == 4'b0001 && priority_out == 2'b00);
    cover (binary_in == 4'b0010 && priority_out == 2'b01);
    cover (binary_in == 4'b0100 && priority_out == 2'b10);
    cover (binary_in == 4'b1000 && priority_out == 2'b11);
    cover ((binary_in == 4'b0000 || $countones(binary_in) != 1) && priority_out == 2'b00);
  end
endmodule

// Assertions + coverage for gray_code_generator
module gray_code_generator_sva (
  input  logic [3:0] priority_in,
  input  logic [3:0] gray_code,
  input  logic [1:0] priority_out
);
  logic [3:0] exp_gray;
  always_comb begin
    exp_gray = {priority_out[1]^priority_out[0], priority_out[1], priority_out[0], priority_out[0]^priority_out[1]};

    assert (gray_code === exp_gray)
      else $error("gray_code mismatch in=%b out=%b exp=%b", priority_in, gray_code, exp_gray);

    assert (gray_code[0] === gray_code[3])
      else $error("gray_code[0] != gray_code[3]");

    if (!$isunknown(priority_out))
      assert (!$isunknown(gray_code))
        else $error("gray_code X/Z with known priority_out");

    // Functional coverage (1-hot inputs and default path)
    cover (priority_in == 4'b0001 && gray_code == 4'b0000);
    cover (priority_in == 4'b0010 && gray_code == 4'b1011);
    cover (priority_in == 4'b0100 && gray_code == 4'b1101);
    cover (priority_in == 4'b1000 && gray_code == 4'b0110);
    cover ((priority_in == 4'b0000 || $countones(priority_in) != 1) && gray_code == 4'b0000);
  end
endmodule

// Bind the SVA to the DUTs
bind priority_encoder     priority_encoder_sva     pe_sva_i (.binary_in(binary_in), .priority_out(priority_out));
bind gray_code_generator  gray_code_generator_sva  gcg_sva_i(.priority_in(priority_in), .gray_code(gray_code), .priority_out(priority_out));