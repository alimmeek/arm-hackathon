module arbiter (
    input  logic clk,
    input  logic resetn,

    input  logic [2:0] r,   // Resource request from each device
    
    output logic [2:0] g    // Status of grants
);

// State machine encoding
parameter A = 2'b00, B = 2'b01, C = 2'b10, D = 2'b11;

logic [1:0] next_state;
logic [1:0] curr_state;

logic [2:0] g_next;
logic [2:0] g_q;


// Decide next state based on current state and which devices (if any) have requested the resource
always_comb begin
    next_state = curr_state;

    case (curr_state)
        A : begin
            if (r[0]) begin
                next_state = B;
            end else if (r[1]) begin
                next_state = C;
            end else if (r[2]) begin
                next_state = D;
            end
        end

        B : begin
            if (~r[0]) begin
                next_state = A;
            end
        end

        C : begin
            if (~r[1]) begin
                next_state = A;
            end
        end

        D : begin
            if (~r[2]) begin
                next_state = A;
            end
        end
    endcase
end

// Allocate resource based on current state
always_comb begin
    g_next = g_q;

    // Use next_state to reduce latency between a state changing and the resource being allocated
    case (next_state)
        A : g_next = 3'b000;

        B : g_next = 3'b001;

        C : g_next = 3'b010;

        D : g_next = 3'b100;
    endcase
end

// Update the current state and grant on each clock cycle
// On resetn, set the state machine to state A and deallocate the resource
always_ff @(posedge clk or negedge resetn) begin
    if (~resetn) begin
        curr_state <= A;
        g_q <= 3'b000;
    end else begin
        curr_state <= next_state;
        g_q <= g_next;
    end
end

assign g = g_q;

endmodule