from django.shortcuts import render

# Create your views here.
def dashboard(request):
    if request.method == 'POST':
        amount = request.POST.get('amount')
        print(amount)
        date = request.POST.get('date')
        print(amount)

        if not amount or not date:
            error_message = "Both amount and date fields are required."
            return render(request, 'dashboard.html', {'error_message': error_message})        

        return render(request, 'dashboard.html', )

    return render(request, 'dashboard.html')