# Moje Drogi

Aplikacja w przeglądarce telefonu (PWA). Nagrywa trasy z GPS, rysuje przejechane drogi na mapie OpenStreetMap i liczy, ile ulic w każdej miejscowości już przejechałeś.

## Ekrany
1. **Mapa**: wszystkie przejechane trasy na niebiesko, bieżąca na pomarańczowo, przerywany okrąg 120 km wokół Krakowa i przycisk nagrywania.
2. **Miejscowości**: lista miejscowości z liczbą ulic, kilometrami i datą ostatniego przejazdu. Tu jest też import plików GPX i kopia zapasowa.
3. **Statystyki**: wybrana miejscowość z procentem przejechanych ulic (po kliknięciu „Policz wszystkie ulice”), listą ulic (przejechane i jeszcze nie) oraz historią przejazdów.

## Jak to działa
- Pozycja GPS jest zapisywana co najmniej co 8 m. Odczyty z dokładnością gorszą niż ±35 m są pomijane.
- Po zakończeniu trasy co ~200 m aplikacja pyta Nominatim (OpenStreetMap) o ulicę i miejscowość, najwyżej 1 zapytanie na sekundę. Długa trasa (100 km) rozpoznaje się ok. 10 minut, gdy aplikacja jest otwarta. Wyniki zostają w pamięci, więc ponowne przejazdy tą samą drogą idą szybko.
- „Policz wszystkie ulice” pobiera z Overpass API listę nazwanych ulic w granicach administracyjnych miejscowości. Aplikacja zawsze pokazuje, w jakich granicach liczyła.
- Wszystkie dane są tylko na telefonie (IndexedDB). Kopia zapasowa to plik `.json`.

## Uruchomienie
GPS w przeglądarce działa tylko na stronach **https://**. Najprościej:
- **Netlify Drop**: wejdź na app.netlify.com/drop i przeciągnij folder `moje-drogi`. Dostaniesz adres https.
- **GitHub Pages**: wrzuć pliki do repozytorium i włącz Pages.

Potem otwórz adres na telefonie i wybierz „Dodaj do ekranu głównego”.

Test na komputerze: `python3 -m http.server 8000` w tym folderze, potem http://localhost:8000.

## Ograniczenia
- Przeglądarka przestaje nagrywać GPS, gdy ekran zgaśnie albo przełączysz aplikację. Aplikacja trzyma ekran włączony podczas nagrywania, więc najlepiej mieć telefon w uchwycie z otwartą aplikacją.
- Kilometry w miejscowości sumują wszystkie przejazdy, więc ta sama droga przejechana dwa razy liczy się podwójnie. Unikalne są ulice.
